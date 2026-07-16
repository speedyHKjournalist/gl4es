#ifndef _GL4ES_ARBCONVERTER_H_
#define _GL4ES_ARBCONVERTER_H_

#include <stdint.h>

typedef struct arb_program_stats_s {
	int instructions;
	int temporaries;
	int parameters;
	int attributes;
	int address_registers;
	int alu_instructions;
	int tex_instructions;
	int tex_indirections;
} arb_program_stats_t;

char* gl4es_convertARB(const char* const code, int vertex, char **error_msg, int *error_ptr);
char* gl4es_convertARBWithStats(const char* const code, int vertex, char **error_msg,
	int *error_ptr, arb_program_stats_t *stats);

#endif // _GL4ES_ARBCONVERTER_H_
