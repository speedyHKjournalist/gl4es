#include "arbconverter.h"

#include <stddef.h>

#include "arbgenerator.h"
#include "arbhelper.h"
#include "arbparser.h"
#include "khash.h"

#define FAIL(str) curStatus.status = ST_ERROR; if (*error_msg) free(*error_msg); \
		*error_msg = strdup(str); continue
#define curStatusPtr &curStatus
static int variableIndex(const sCurStatus *status, const sVariable *var) {
	for (size_t i = 0; i < status->variables.size; ++i) {
		if (status->variables.vars[i] == var)
			return (int)i;
	}
	return -1;
}

static int variableIsDestination(const sCurStatus *status, const sVariable *var) {
	for (size_t i = 0; i < status->instructions.size; ++i) {
		const sInstruction *inst = status->instructions.insts[i];
		if (inst->type != INST_KIL && inst->vars[0].var == var)
			return 1;
	}
	return 0;
}

static int implicitAttribute(const sVariable *var, int vertex) {
	if (!var->init.strings_count)
		return 0;
	const char *value = var->init.strings[0];
	if (vertex)
		return !strcmp(value, "gl_Vertex") || !strcmp(value, "gl_Normal") ||
		       !strcmp(value, "gl_Color") || !strcmp(value, "gl_SecondaryColor") ||
		       !strcmp(value, "gl_FogCoord") || !strncmp(value, "gl_MultiTexCoord", 16) ||
		       !strncmp(value, "gl_VertexAttrib_", 16);
	return !strcmp(value, "gl_Color") || !strcmp(value, "gl_SecondaryColor") ||
	       !strncmp(value, "gl_TexCoord[", 12) || !strcmp(value, "gl_FragCoord") ||
	       !strncmp(value, "vec4(gl_FogFragCoord", 20);
}

static int earlierImplicitBinding(const sCurStatus *status, size_t current,
	const sVariable *var, int vertex, int attribute) {
	if (!var->init.strings_count)
		return 0;
	for (size_t i = 0; i < current; ++i) {
		const sVariable *other = status->variables.vars[i];
		if (other->type != VARTYPE_CONST || !other->init.strings_count ||
		    variableIsDestination(status, other) ||
		    implicitAttribute(other, vertex) != attribute)
			continue;
		if (!strcmp(other->init.strings[0], var->init.strings[0]))
			return 1;
	}
	return 0;
}

static void collectProgramStats(const sCurStatus *status, int vertex,
	arb_program_stats_t *stats) {
	memset(stats, 0, sizeof(*stats));
	stats->instructions = (int)status->instructions.size;
	stats->tex_indirections = vertex ? 0 : 1;

	for (size_t i = 0; i < status->variables.size; ++i) {
		const sVariable *var = status->variables.vars[i];
		switch (var->type) {
		case VARTYPE_TEMP:
			++stats->temporaries;
			break;
		case VARTYPE_PARAM:
			++stats->parameters;
			break;
		case VARTYPE_PARAM_MULT:
			stats->parameters += var->size > 0 ? var->size : (int)var->init.strings_count;
			break;
		case VARTYPE_ATTRIB:
			++stats->attributes;
			break;
		case VARTYPE_ADDRESS:
			++stats->address_registers;
			break;
		default:
			break;
		}
	}
	for (size_t i = 0; i < status->variables.size; ++i) {
		const sVariable *var = status->variables.vars[i];
		if (var->type != VARTYPE_CONST || variableIsDestination(status, var))
			continue;
		int attribute = implicitAttribute(var, vertex);
		if (earlierImplicitBinding(status, i, var, vertex, attribute))
			continue;
		if (attribute)
			++stats->attributes;
		else
			++stats->parameters;
	}

	/* ARB_fragment_program issue 24 defines texture indirections as nodes
	 * separated when a texture instruction conflicts with temporaries used in
	 * the current node.  Track those sets by parsed temporary identity. */
	unsigned char *tex_outputs = calloc(status->variables.size, 1);
	unsigned char *alu_temps = calloc(status->variables.size, 1);
	if (status->variables.size && (!tex_outputs || !alu_temps)) {
		free(tex_outputs);
		free(alu_temps);
		return;
	}
	for (size_t i = 0; i < status->instructions.size; ++i) {
		const sInstruction *inst = status->instructions.insts[i];
		if (INSTTEX(inst->type)) {
			++stats->tex_instructions;
			int input = variableIndex(status, inst->vars[1].var);
			int output = variableIndex(status, inst->vars[0].var);
			int split = input >= 0 && inst->vars[1].var->type == VARTYPE_TEMP && tex_outputs[input];
			split |= output >= 0 && inst->vars[0].var->type == VARTYPE_TEMP && alu_temps[output];
			if (!vertex && split) {
				++stats->tex_indirections;
				memset(tex_outputs, 0, status->variables.size);
				memset(alu_temps, 0, status->variables.size);
			}
			if (output >= 0 && inst->vars[0].var->type == VARTYPE_TEMP)
				tex_outputs[output] = 1;
		} else {
			++stats->alu_instructions;
			if (inst->type == INST_KIL) {
				int input = variableIndex(status, inst->vars[0].var);
				if (input >= 0 && inst->vars[0].var->type == VARTYPE_TEMP)
					alu_temps[input] = 1;
				continue;
			}
			for (int operand = 1; operand < MAX_OPERANDS && inst->vars[operand].var; ++operand) {
				int input = variableIndex(status, inst->vars[operand].var);
				if (input >= 0 && inst->vars[operand].var->type == VARTYPE_TEMP)
					alu_temps[input] = 1;
			}
			int output = variableIndex(status, inst->vars[0].var);
			if (output >= 0 && inst->vars[0].var->type == VARTYPE_TEMP) {
				alu_temps[output] = 1;
				tex_outputs[output] = 1;
			}
		}
	}
	free(tex_outputs);
	free(alu_temps);
}

char* gl4es_convertARBWithStats(const char* const code, int vertex, char **error_msg,
	int *error_ptr, arb_program_stats_t *stats) {
	*error_ptr = -1; // Reinit error pointer
	if (stats)
		memset(stats, 0, sizeof(*stats));
	
	struct sSpecialCases specialCases = {0};
	const char *codeStart = code;
	// Not sure this is really OK...
	if ((codeStart[0] != '!') || (codeStart[1] != '!')) {
		while (1) {
			while ((*codeStart != '!') && (*codeStart != '\0')) {
				++codeStart;
			}
			if (*codeStart == '\0') {
				// Invalid start
				if (*error_msg)
					free(*error_msg);
				*error_msg = strdup("Invalid program start");
				*error_ptr = 0;
				return NULL;
			}
			if ((codeStart[0] == '!') && (codeStart[1] == '!')) {
				break;
			}
			++codeStart;
		}
	}
	if (vertex) {
		if (strncmp(codeStart, "!!ARBvp1.0", 10)) {
			if (*error_msg)
				free(*error_msg);
			*error_msg = strdup("Invalid program start");
			*error_ptr = codeStart - code;
			return NULL;
		}
	} else {
		if (strncmp(codeStart, "!!ARBfp1.0", 10)) {
			if (*error_msg)
				free(*error_msg);
			*error_msg = strdup("Invalid program start");
			*error_ptr = codeStart - code;
			return NULL;
		}
	}
	
	codeStart += 10;
	
	ARBCONV_DBG_HEAVY(printf("Generating code for:\n%s\n", codeStart);)
	
	sCurStatus curStatus = {0};
	initStatus(&curStatus, codeStart);
	readNextToken(&curStatus);
	if ((curStatus.curToken != TOK_NEWLINE) && (curStatus.curToken != TOK_WHITESPACE)) {
		curStatus.status = ST_ERROR;
	} else {
		readNextToken(&curStatus);
	}
	
	while ((curStatus.status != ST_ERROR) && (curStatus.status != ST_DONE)) {
		ARBCONV_DBG_LP(
			printf(
				"%-13s",
				STATUS2STR(curStatus.status)
			);
			if (curStatus.valueType == TYPE_INST_DECL) {
				printf(
					"-%3s%4s    (%2d)",
					INST2STR(curStatus.curValue.newInst.inst.type),
					curStatus.curValue.newInst.inst.saturated ? "_SAT" : "    ",
					curStatus.curValue.newInst.state
				);
			} else if (curStatus.valueType == TYPE_VARIABLE_DECL) {
				printf(
					"-%-10s (%2d)",
					VARTYPE2STR(curStatus.curValue.newVar.var->type),
					curStatus.curValue.newVar.state
				);
			} else if (curStatus.valueType == TYPE_ALIAS_DECL) {
				printf("-(string)       ");
			} else if (curStatus.valueType == TYPE_OPTION_DECL) {
				printf("-%15s", curStatus.curValue.newOpt.optName ? curStatus.curValue.newOpt.optName : "");
			} else {
				printf("                ");
			}
			printf(" / %-11s: %p - %p (%ld)\n",
				TOKEN2STR(curStatus.curToken),
				curStatus.codePtr,
				curStatus.endOfToken,
				curStatus.endOfToken - curStatus.codePtr
			);
			fflush(stdout);
		)
		
		parseToken(&curStatus, vertex, error_msg, &specialCases);
		
		readNextToken(&curStatus);
	}
	
	if (curStatus.status == ST_ERROR) {
		ARBCONV_DBG(
		char *codeDup = strdup(code);
		codeDup[curStatus.codePtr - code] = '\0';
		printf(
			"Failure, copy until EOF\n\n%s\033[91m%s\033[m\n",
			codeDup,
			curStatus.codePtr
		);
		free(codeDup);
		
		printf("\nVariables:\n==========\n");
		{
			const char *kvar;
			sVariable *vvar;
			kh_foreach(curStatus.varsMap, kvar, vvar, 
				if (vvar) {
					printf("Variable %10s pointing to %p (%10s)\n", kvar, vvar, vvar->names[0]);
				} else {
					printf("\033[91mVariable %10s pointing to NULLptr!\033[m\n", kvar);
				}
			)
		}
		for (size_t i = 0; i < curStatus.variables.size; ++i) {
			sVariable *varPtr = curStatus.variables.vars[i];
			printf("Variable %p %10s (%lu): %-10s (init = %3lu %s)\n", varPtr, varPtr->names[0], varPtr->names_count, VARTYPE2STR(varPtr->type), varPtr->init.strings_total_len, varPtr->init.strings_count ? varPtr->init.strings[0] : "(none)");
		}
		printf("\nInstructions:\n=============\n");
		for (size_t i = 0; i < curStatus.instructions.size; ++i) {
			sInstruction *instPtr = curStatus.instructions.insts[i];
			instPtr = curStatus.instructions.insts[i];
			if (INSTTEX(instPtr->type)) {
				printf("Instruction %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %ctexture[%2s]      %c%19s\n", INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
					instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var->names[0],
					instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', (instPtr->vars[3].var == curStatus.tex1D) ? "1D" : (instPtr->vars[3].var == curStatus.tex2D) ? "2D" : (instPtr->vars[3].var == curStatus.tex3D) ? "3D" : (instPtr->vars[3].var == curStatus.texCUBE) ? "CUBE" : (instPtr->vars[3].var == curStatus.texRECT) ? "RECT" : "!!!"
				);
			} else {
				printf("Instruction %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c\n", INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
					instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var ? ((instPtr->vars[2].var->type == VARTYPE_CONST) ? instPtr->vars[2].var->init.strings[0] : instPtr->vars[2].var->names[0]) : "(none)", instPtr->vars[2].floatArrAddr ? instPtr->vars[2].floatArrAddr : "", (instPtr->vars[2].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', instPtr->vars[3].var ? ((instPtr->vars[3].var->type == VARTYPE_CONST) ? instPtr->vars[3].var->init.strings[0] : instPtr->vars[3].var->names[0]) : "(none)", instPtr->vars[3].floatArrAddr ? instPtr->vars[3].floatArrAddr : "", (instPtr->vars[3].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[3] == SWIZ_W) ? 'w' : ' '
				);
			}
		}
		printf("\n");)
		
		*error_ptr = curStatus.codePtr - code;
		
		// We have errored, output NULL
		freeStatus(&curStatus);
		free(curStatus.outputString);
		return NULL;
	}
	
	ARBCONV_DBG(printf("Success!\n");)
	
	// Variables are automatically created, only need to write main()
	size_t varIdx = (size_t)0;
	sVariable *varPtr;
	size_t instIdx = (size_t)0;
	sInstruction *instPtr;
	
	do {
		if (vertex) {
			// Add a structure (for addresses) with only an 'x' component
			APPEND_OUTPUT("#version 120\n\nstruct _structOnlyX { int x; };\n\nvoid main() {\n", 61)
			if (specialCases.hasFogFragCoord) {
				APPEND_OUTPUT("\tvec4 gl4es_FogFragCoordTemp = vec4(gl_FogFragCoord);\n", 54)
			}
			if (specialCases.hasPointSize) {
				APPEND_OUTPUT2("\tvec4 gl4es_PointSizeTemp = vec4(gl_PointSize, 0., 0., 0.);\n")
			}
		} else {
			// No address
			APPEND_OUTPUT("#version 120\n\nvoid main() {\n", 28)
			if (specialCases.isDepthReplacing) {
				APPEND_OUTPUT("\tvec4 gl4es_FragDepthTemp = vec4(gl_FragDepth);\n", 48)
			}
		}
		
		for (; (varIdx < curStatus.variables.size) && (curStatus.status != ST_ERROR); ++varIdx) {
			varPtr = curStatus.variables.vars[varIdx];
			
			ARBCONV_DBG_AS(
				printf("Variable #%2ld: %10s (%10s)\n", varIdx, varPtr->names[0], VARTYPE2STR(varPtr->type));
				fflush(stdout);
			)
			
			generateVariablePre(&curStatus, vertex, error_msg, varPtr);
		}
		if (curStatus.status == ST_ERROR) {
			--varIdx;
			*error_ptr = 1;
			break;
		}
		
		APPEND_OUTPUT("\t\n", 2)
		for (; (instIdx < curStatus.instructions.size) && (curStatus.status != ST_ERROR); ++instIdx) {
			instPtr = curStatus.instructions.insts[instIdx];
			
			ARBCONV_DBG_AS(
				if (INSTTEX(instPtr->type)) {
					printf("Instruction #%3ld: %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %ctexture[%2s]      %c%19s\n", instIdx, INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
						instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
						instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
						instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var->names[0],
						instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', (instPtr->vars[3].var == curStatus.tex1D) ? "1D" : (instPtr->vars[3].var == curStatus.tex2D) ? "2D" : (instPtr->vars[3].var == curStatus.tex3D) ? "3D" : (instPtr->vars[3].var == curStatus.texCUBE) ? "CUBE" : (instPtr->vars[3].var == curStatus.texRECT) ? "RECT" : "!!!"
					);
				} else {
					printf("Instruction #%3ld: %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c\n", instIdx, INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
						instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
						instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
						instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var ? ((instPtr->vars[2].var->type == VARTYPE_CONST) ? instPtr->vars[2].var->init.strings[0] : instPtr->vars[2].var->names[0]) : "(none)", instPtr->vars[2].floatArrAddr ? instPtr->vars[2].floatArrAddr : "", (instPtr->vars[2].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[3] == SWIZ_W) ? 'w' : ' ',
						instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', instPtr->vars[3].var ? ((instPtr->vars[3].var->type == VARTYPE_CONST) ? instPtr->vars[3].var->init.strings[0] : instPtr->vars[3].var->names[0]) : "(none)", instPtr->vars[3].floatArrAddr ? instPtr->vars[3].floatArrAddr : "", (instPtr->vars[3].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[3] == SWIZ_W) ? 'w' : ' '
					);
				}
				fflush(stdout);
			)
			
			generateInstruction(&curStatus, vertex, error_msg, instPtr);
		}
		if (curStatus.status == ST_ERROR) {
			--instIdx;
			*error_ptr = curStatus.instructions.insts[instIdx]->codeLocation - code;
			break;
		}
		
		APPEND_OUTPUT("\t\n", 2)
		for (varIdx = 0; (varIdx < curStatus.variables.size) && (curStatus.status != ST_ERROR); ++varIdx) {
			varPtr = curStatus.variables.vars[varIdx];
			
			ARBCONV_DBG_AS(
				printf("Variable #%2ld (output): %10s (%10s)\n", varIdx, varPtr->names[0], VARTYPE2STR(varPtr->type));
				fflush(stdout);
			)
			
			generateVariablePst(&curStatus, vertex, error_msg, varPtr);
		}
		if (curStatus.status == ST_ERROR) {
			--varIdx;
			*error_ptr = 2;
			break;
		}
		
		if (specialCases.hasFogFragCoord) {
			APPEND_OUTPUT("\tgl_FogFragCoord = gl4es_FogFragCoordTemp.x;\n", 45)
		}
		if (specialCases.hasPointSize) {
			APPEND_OUTPUT2("\tgl_PointSize = gl4es_PointSizeTemp.x;\n")
		}
		if (specialCases.isDepthReplacing) {
			APPEND_OUTPUT("\tgl_FragDepth = gl4es_FragDepthTemp.z;\n", 39)
		}
		switch (curStatus.fogType) {
		case FOG_NONE:
			break;
		case FOG_EXP:
			APPEND_OUTPUT(
				"\tgl_FragColor.rgb = mix(gl_Fog.color.rgb, gl_FragColor.rgb, "
				"clamp(exp(-gl_Fog.density * gl_FogFragCoord), 0., 1.));\n",
				116
			)
			break;
		case FOG_EXP2:
			APPEND_OUTPUT(
				"\tgl_FragColor.rgb = mix(gl_Fog.color.rgb, gl_FragColor.rgb, "
				"clamp(exp(-(gl_Fog.density * gl_FogFragCoord)*(gl_Fog.density * gl_FogFragCoord)), 0., 1.));\n",
				153
			)
			break;
		case FOG_LINEAR:
			APPEND_OUTPUT(
				"\tgl_FragColor.rgb = mix(gl_Fog.color.rgb, gl_FragColor.rgb, "
				"clamp((gl_Fog.end - gl_FogFragCoord) * gl_Fog.scale, 0., 1.));\n",
				123
			)
			break;
		}
		if(curStatus.position_invariant) {
			APPEND_OUTPUT("\tgl_Position = ftransform();\n", 29)
		}
		APPEND_OUTPUT("}\n", 2)
	} while (0);
	
#undef FAIL
#undef APPEND_OUTPUT
#undef APPEND_OUTPUT2
	
	if (curStatus.status == ST_ERROR) {
		ARBCONV_DBG(printf("Failure!\n");
		
		printf("\nVariables:\n==========\n");
		{
			const char *kvar;
			sVariable *vvar;
			kh_foreach(curStatus.varsMap, kvar, vvar, 
				if (vvar) {
					printf("Variable %10s pointing to %p (%10s)\n", kvar, vvar, vvar->names[0]);
				} else {
					printf("\033[91mVariable %10s pointing to NULLptr!\033[m\n", kvar);
				}
			)
		}
		for (size_t i = 0; i < curStatus.variables.size; ++i) {
			varPtr = curStatus.variables.vars[i];
			printf("%sVariable %p %10s (%lu): %-10s (init = %3lu %s)\033[m\n", (i < varIdx) ? "" : "\033[91m", varPtr, varPtr->names[0], varPtr->names_count, VARTYPE2STR(varPtr->type), varPtr->init.strings_total_len, varPtr->init.strings_count ? varPtr->init.strings[0] : "(none)");
		}
		printf("\nInstructions:\n=============\n");
		for (size_t i = 0; i < curStatus.instructions.size; ++i) {
			instPtr = curStatus.instructions.insts[i];
			if (INSTTEX(instPtr->type)) {
				printf("%sInstruction %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %ctexture[%2s]      %c%19s\033[m\n", (i < instIdx) ? "" : "\033[91m", INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
					instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var->names[0],
					instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', (instPtr->vars[3].var == curStatus.tex1D) ? "1D" : (instPtr->vars[3].var == curStatus.tex2D) ? "2D" : (instPtr->vars[3].var == curStatus.tex3D) ? "3D" : (instPtr->vars[3].var == curStatus.texCUBE) ? "CUBE" : (instPtr->vars[3].var == curStatus.texRECT) ? "RECT" : "!!!"
				);
			} else {
				printf("%sInstruction %3s%4s %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c %c%10s[%2s].%c%c%c%c\033[m\n", (i < instIdx) ? "" : "\033[91m", INST2STR(instPtr->type), instPtr->saturated ? "_SAT" : "    ",
					instPtr->vars[0].sign ? (instPtr->vars[0].sign == -1 ? '-' : '+') : ' ', instPtr->vars[0].var ? ((instPtr->vars[0].var->type == VARTYPE_CONST) ? instPtr->vars[0].var->init.strings[0] : instPtr->vars[0].var->names[0]) : "(none)", instPtr->vars[0].floatArrAddr ? instPtr->vars[0].floatArrAddr : "", (instPtr->vars[0].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[0].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[0].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[0].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[0].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[1].sign ? (instPtr->vars[1].sign == -1 ? '-' : '+') : ' ', instPtr->vars[1].var ? ((instPtr->vars[1].var->type == VARTYPE_CONST) ? instPtr->vars[1].var->init.strings[0] : instPtr->vars[1].var->names[0]) : "(none)", instPtr->vars[1].floatArrAddr ? instPtr->vars[1].floatArrAddr : "", (instPtr->vars[1].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[1].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[1].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[1].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[1].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[2].sign ? (instPtr->vars[2].sign == -1 ? '-' : '+') : ' ', instPtr->vars[2].var ? ((instPtr->vars[2].var->type == VARTYPE_CONST) ? instPtr->vars[2].var->init.strings[0] : instPtr->vars[2].var->names[0]) : "(none)", instPtr->vars[2].floatArrAddr ? instPtr->vars[2].floatArrAddr : "", (instPtr->vars[2].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[2].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[2].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[2].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[2].swizzle[3] == SWIZ_W) ? 'w' : ' ',
					instPtr->vars[3].sign ? (instPtr->vars[3].sign == -1 ? '-' : '+') : ' ', instPtr->vars[3].var ? ((instPtr->vars[3].var->type == VARTYPE_CONST) ? instPtr->vars[3].var->init.strings[0] : instPtr->vars[3].var->names[0]) : "(none)", instPtr->vars[3].floatArrAddr ? instPtr->vars[3].floatArrAddr : "", (instPtr->vars[3].swizzle[0] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[0] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[0] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[0] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[1] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[1] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[1] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[1] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[2] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[2] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[2] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[2] == SWIZ_W) ? 'w' : ' ', (instPtr->vars[3].swizzle[3] == SWIZ_X) ? 'x' : (instPtr->vars[3].swizzle[3] == SWIZ_Y) ? 'y' : (instPtr->vars[3].swizzle[3] == SWIZ_Z) ? 'z' : (instPtr->vars[3].swizzle[3] == SWIZ_W) ? 'w' : ' '
				);
			}
		}
		
		printf("\nBuffered output:\n%s\n", curStatus.outputString);)
		
		if (*error_ptr == -1) {
			if (*error_msg)
				free(*error_msg);
			*error_msg = strdup("Not enough memory(?)");
			*error_ptr = 0;
		}
		
		// We have errored, output NULL
		freeStatus(&curStatus);
		free(curStatus.outputString);
		return NULL;
	}
	
	ARBCONV_DBG(printf("Success!\n\nOutput:\n%s", curStatus.outputString);)
	if (stats)
		collectProgramStats(&curStatus, vertex, stats);
	
	freeStatus(&curStatus);
	return curStatus.outputString;
}

char* gl4es_convertARB(const char* const code, int vertex, char **error_msg, int *error_ptr) {
	return gl4es_convertARBWithStats(code, vertex, error_msg, error_ptr, NULL);
}
