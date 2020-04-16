/*
 * Transmeta TM5xxx disassembler
 *  
 * This is a full disassembler and analysis toolset for TM58xx CMS images.
 * This program was designed and tested under Linux only. It will take an
 * appropriately decompressed and padded CMS binary image (see "Obtaining
 * CMS Memory Images" in the accompanying report) and disassemble it, 
 * complete with basic block analysis and statistical report generation. 
 *
 * This program is licensed under the GNU General Public License.
 */
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <assert.h>

#define byte char
#define W32 unsigned long int
#define W32s signed long int
#define W64 unsigned long long int

#define bits(x, i, l) (((x) >> (i)) & ((1 << (l))-1))
#define bit(x, i) bits((x), (i), 1)

static inline W32s signext(W32s x, const int i) { return (x << (32-i)) >> (32-i); }
static inline W32s bitsext(W32s x, const int i, const int l) { return signext(bits(x, i, l), l); }

inline W32 hi32(W64 x) { return (W32)(x >> 32LL); }
inline W32 lo32(W64 x) { return (W32)(x & 0xffffffffLL); }

char* binstr(char* buf, W32 x, int n) {
  for (int i = 0; i < n; i++) {
    buf[(n-1)-i] = ((int)((x >> i) & 1)) + '0';
  }
  buf[n] = 0;
  return buf;
}

char* binstr(W32 x, int n) {
  static char buf[33];
  return binstr(buf, x, n);
}

typedef char binstrbuf_t[64];

/*
 * TM5xxx/TM32xx instruction format
 */
typedef union Insn {
	struct { W32 unknown:2, rb:6, ra:6, rd:6, op:9, type:3; } alu;
	struct { W32 imm:8, ra:6, rd:6, op:9, type:3; } aluimm8;
	struct { W32 unknown:2, rb:6, ra:6, rd:6, op:9, type:3; } lsu;
	struct { W32 offset:23, ind:1, unknown1:1, cond:4, type:3; } br;
	struct { W32 unknown3:1, ra:6, unknown2:16, ind:1, unknown1:1, cond:4, type:3; } brreg;
	W32 imm;
  Insn(W32 data) { imm = data; }
  operator W32() const { return imm; }
} Insn;

int lsu_insns_in_a_row = 0;
int bru_insns_in_a_row = 0;
int last_bru_insn_cond = 0;
int saved_bru_insn_cond = 0;

bool alu0_used, alu1_used, lsu_used, bru_used;

static const char* regnames[64] = {
  "%r0", "%r1", "%r2", "%r3", "%r4", "%r5", "%r6", "%r7",
  "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15",
  "%r16", "%r17", "%r18", "%r19", "%r20", "%r21", "%r22", "%r23",
  "%r24", "%r25", "%r26", "%r27", "%r28", "%r29", "%r30", "%r31",
  "%r32", "%r33", "%r34", "%r35", "%r36", "%r37", "%r38", "%r39",
  "%r40", "%r41", "%r42", "%r43", "%r44", "%r45", "%r46", "%sp",
  "%r48", "%r49", "%r50", "%r51", "%r52", "%r53", "%r54", "%r55",
  "%r56", "%r57", "%link", "%from", "%r60", "%r61", "%sink", "%zero"
};

#define _ 0

/*
 * Primary opcode map:
 * - high 6 bits in rows, low 3 bits in columns
 * - '0' = used but as yet unknown
 * - '_' = unused in CMS image
 * - 'xxxi' = uses 8-bit immediate
 * - 'xxxil' = uses 32-bit immediate
 * - 'xxx.c' = sets condition codes
 */ 
static const char* insn_name_table[1<<9] = {
//         000        001        010        011        100        101        110        111
/*000000*/ 0,         0,         _,         _,         _,         _,         _,         _,         
/*000001*/ 0,         0,         0,         0,         _,         _,         0,         0,
/*000010*/ 0,         _,         0,         0,         0,         _,         _,         _,
/*000011*/ 0,         _,         0,         0,         _,         _,         _,         _,
/*000100*/ "cmpand",  0,         _,         0,         _,         _,         _,         _,
/*000101*/ 0,         0,         _,         0,         0,         _,         _,         _,
/*000110*/ 0,         0,         _,         0,         _,         _,         _,         _,
/*000111*/ 0,         0,         0,         "lsunop",  _,         _,         _,         _,
/*001000*/ 0,         _,         _,         0,         "st",      _,         _,         _,
/*001001*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*001010*/ "ld",      _,         _,         0,         0,         _,         _,         _,
/*001011*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*001100*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*001101*/ "movlink", _,         _,         0,         0,         _,         _,         _,
/*001110*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*001111*/ 0,         _,         _,         0,         0,         _,         _,         _,

/*010000*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*010001*/ 0,         0,         0,         0,         0,         _,         _,         _,
/*010010*/ 0,         0,         0,         "slli",    0,         0,         0,         0,
/*010011*/ 0,         0,         0,         0,         0,         _,         _,         0,
/*010100*/ 0,         0,         _,         0,         0,         _,         _,         _,
/*010101*/ _,         0,         0,         0,         0,         _,         _,         0,
/*010110*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*010111*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*011000*/ 0,         _,         _,         _,         _,         0,         0,         0,
/*011001*/ 0,         _,         _,         0,         _,         _,         _,         _,
/*011010*/ 0,         0,         0,         0,         0,         0,         0,         0,
/*011011*/ _,         _,         _,         _,         0,         _,         _,         _,
/*011100*/ 0,         _,         _,         _,         _,         _,         _,         _,
/*011101*/ 0,         _,         _,         0,         _,         _,         _,         _,
/*011110*/ 0,         _,         _,         _,         _,         0,         0,         0,
/*011111*/ _,         _,         _,         _,         _,         _,         _,         _,

/*100000*/ "add?",    0,         0,         "addi",    0,         0,         0,         0,
/*100001*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*100010*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*100011*/ "oprr",    0,         0,         0,         0,         _,         _,         _,
/*100100*/ "and",     0,         0,         "andi",    0,         0,         _,         0,
/*100101*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*100110*/ 0,         _,         _,         0,         0,         0,         0,         0,
/*100111*/ "move",    0,         0,         "ori",     0,         _,         _,         0,
/*101000*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*101001*/ 0,         _,         _,         "nop",     0,         _,         _,         _,
/*101010*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*101011*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*101100*/ 0,         0,         0,         "?i.c",    0,         _,         _,         _,
/*101101*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*101110*/ "sub.c",   0,         0,         "cmpi.c",  0,         _,         _,         _,
/*101111*/ 0,         _,         _,         0,         _,         _,         _,         _,

/*110000*/ _,         _,         0,         "addil",   _,         _,         0,         _,
/*110001*/ 0,         _,         _,         _,         _,         _,         _,         _,
/*110010*/ 0,         _,         _,         "?il",     _,         _,         _,         _,
/*110011*/ 0,         0,         0,         "?il.c",   0,         _,         _,         _,
/*110100*/ 0,         0,         0,         "andil",   0,         _,         _,         0,
/*110101*/ "or?",     "?i",      0,         "?il",     0,         _,         _,         _,
/*110110*/ 0,         _,         _,         "?il.c",   0,         _,         0,         0,
/*110111*/ 0,         0,         0,         "moveil",  0,         _,         _,         _,
/*111000*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*111001*/ 0,         _,         _,         "?il",     0,         _,         _,         _,
/*111010*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*111011*/ 0,         _,         _,         _,         0,         _,         _,         _,
/*111100*/ 0,         _,         0,         "?il.c",   _,         _,         _,         _,
/*111101*/ 0,         _,         _,         0,         0,         _,         _,         _,
/*111110*/ 0,         _,         0,         "cmpil.c", _,         _,         _,         _,
/*111111*/ 0,         _,         _,         0,         _,         _,         _,         0,
};

#undef _

#define OP_ALU_NOP 0x14b
#define OP_LSU_NOP 0x3b

int opcode_histogram_alu0[1<<9];
int opcode_histogram_alu1[8][1<<9];
int opcode_histogram_lsu[1<<9];

int total_insns = 0;
int total_nops = 0;

#define OP_USES_IMM32_MASK  0x187 // 11xxxx111
#define OP_USES_IMM32_VALUE 0x183 // 11xxxx011
inline bool op_uses_imm32(W32 op, int aluid) { return ((op & OP_USES_IMM32_MASK) == OP_USES_IMM32_VALUE) && (aluid == 0); }

void print_alu_insn(W32 insnbits, int aluid, W32 imm32 = 0) {
  binstrbuf_t typestr, opcodestr, opcodestr2, rdstr, rastr, rbimmstr;
  Insn insn = insnbits;
  bool is_nop = (insn.alu.op == OP_ALU_NOP);
  total_insns++;
  if (is_nop) total_nops++;
  bool has_imm32 = op_uses_imm32(insn.alu.op, aluid);

  if (aluid == 0) 
    opcode_histogram_alu0[insn.alu.op]++;
  else if (aluid == 1) 
    opcode_histogram_alu1[insn.alu.type][insn.alu.op]++;

  printf("  %s%d %08x = %s %s %s %s %s   # ", (is_nop) ? "nop" : "ALU", aluid, insn.imm, 
         binstr(typestr, insn.alu.type, 3),
         binstr(opcodestr, insn.alu.op, 9),
         binstr(rdstr, insn.alu.rd, 6),
         binstr(rastr, insn.alu.ra, 6),
         binstr(rbimmstr, insn.aluimm8.imm, 8));

  if (is_nop) {
    printf("nop\n");
  } else {
    char opnamebuf[16];

    if (insn_name_table[insn.alu.op])
      snprintf(opnamebuf, sizeof(opnamebuf), "%s", insn_name_table[insn.alu.op]);
    else snprintf(opnamebuf, sizeof(opnamebuf), "%s", binstr(insn.alu.op, 9));

    printf("%-13s", opnamebuf);

    printf("%s,%s,", regnames[insn.alu.rd], regnames[insn.alu.ra]);

    if (has_imm32) {
      printf("0x%08x\n", imm32);
    } else {
      printf("%s/%d\n", regnames[insn.alu.rb], signext(insn.aluimm8.imm, 8));
    }
  }

  alu0_used = !is_nop;
}

void print_alu0_insn(W32 insn, W32 imm32 = 0) {
  print_alu_insn(insn, 0, imm32);
}

void print_alu1_insn(W32 insn) {
  print_alu_insn(insn, 1);
}

void print_lsu_insn(Insn insn) {
  binstrbuf_t typestr, opcodestr, rdstr, rastr, rbimmstr;
  bool is_nop = (insn.lsu.op == OP_LSU_NOP);
  total_insns++;
  if (is_nop)
    total_nops++;
  opcode_histogram_lsu[insn.lsu.op]++;

  printf("  %s %08x = %s %s %s %s %s   # ", (is_nop) ? "nopl" : "LSU ", insn.imm,
         binstr(typestr, insn.lsu.type, 3),
         binstr(opcodestr, insn.lsu.op, 9),
         binstr(rdstr, insn.lsu.rd, 6),
         binstr(rastr, insn.lsu.ra, 6),
         binstr(rbimmstr, insn.aluimm8.imm, 8));
  if (is_nop) {
    printf("nop.lsu\n");
  } else {
    char opnamebuf[16];

    if (insn_name_table[insn.lsu.op])
      snprintf(opnamebuf, sizeof(opnamebuf), "%s", insn_name_table[insn.lsu.op]);
    else snprintf(opnamebuf, sizeof(opnamebuf), "%s", binstr(insn.lsu.op, 9));

    printf("%-13s", opnamebuf);

    printf("%s,%s,[%s]\n", regnames[insn.lsu.rd], regnames[insn.alu.ra], regnames[insn.lsu.rb]);
  }

  lsu_used = !is_nop;
}

// see Intel manual, p861:
static const char* br_cond_name[16] = {
  "o",    "no",   "lt",   "ge",
  "eq",   "ne",   "le",   "gt",
  "s",    "ns",   "pe",   "po",
  "lt.s", "ge.s", "le.s", "gt.s",
};

void print_bru_insn(Insn insn) {
  binstrbuf_t typestr, condstr, offsetstr, unknownstr, regstr;
  char insnstr[64];

  printf("  BRU  %08x = %s %s %s %s ", insn.imm, binstr(typestr, insn.br.type, 3), binstr(condstr, insn.br.cond, 4), (insn.br.unknown1) ? "1" : "0", (insn.br.ind) ? "1" : "0");
  if (insn.br.ind) {
    printf("%s %s %s # ", binstr(unknownstr, insn.brreg.unknown2, 16), binstr(regstr, insn.brreg.ra, 6), insn.brreg.unknown3 ? "1" : "0");
  } else {
    printf("%s   # ", binstr(offsetstr, insn.br.offset, 23));
  }

  switch (insn.br.type) {
  case 4: // 0b100: unconditional branch
    snprintf(insnstr, sizeof(insnstr), "br%s%s", bit(insn.br.cond, 1) ? ".link" : "", (insn.br.unknown1) ? ".u1" : "");
    break;
  case 5: // 0b101: conditional branch
    snprintf(insnstr, sizeof(insnstr), "br.%s%s", br_cond_name[insn.br.cond], (insn.br.unknown1) ? ".u1" : "");
    break;
  default:
    snprintf(insnstr, sizeof(insnstr), "br.%d%s", insn.br.type, (insn.br.unknown1) ? ".u1" : "");
    break;
  }

  if (insn.br.ind) {
    printf("%-12s %s", insnstr, regnames[insn.brreg.ra]);
    if (insn.brreg.unknown3) printf(",u3");
    if (insn.brreg.unknown2) printf(",%s", binstr(offsetstr, insn.brreg.unknown2, 16));
    printf("\n");
  } else {
    printf("%-12s 0x%08x\n", insnstr, (insn.br.offset << 3));
  }

  total_insns++;
  last_bru_insn_cond = insn.br.cond;
  if (insn.br.type == 5) bru_used = true;
}

#define CODE_SEG_START 0x8e000
#define DATA_SEG_START 0x1823f0

#define BUNDLE_TYPE_LSU_ALU1_ALU0_IMM32 0
#define BUNDLE_TYPE_LSU_ALU1_ALU0_BRU   1
#define BUNDLE_TYPE_LSU_ALU1            2
#define BUNDLE_TYPE_ALU0_IMM32          3
#define BUNDLE_TYPE_ALU0_ALU1           4
#define BUNDLE_TYPE_ALU0_BRU            5
int bundle_type_histogram[6];

#define COLBITS 3

void print_opcode_histogram(const char* name, int* stats) {
  printf("%s\n", name);
  printf("              ");
  for (int i = 0; i < (1<<COLBITS); i++) {
    binstrbuf_t lowbits;
    printf("%-10s ", binstr(lowbits, i, COLBITS));
  }
  printf("\n");

  for (int i = 0; i < (1<<9); i++) {
    if (bits(i, 0, COLBITS) == 0) {
      binstrbuf_t highbits;
      printf("  %9s:  ", binstr(highbits, bits(i, COLBITS, 9-COLBITS), 9-COLBITS));
    }
    printf("%-10d ", stats[i]);
    if (bits(i, 0, COLBITS) == (1<<COLBITS)-1) {
      printf("\n");
    }
  }
  printf("\n");
}

int main(int argc, char* argv[]) {
  FILE* fd = fopen(argv[1], "r");
  fseek(fd, 0, SEEK_END);
  int count = ftell(fd);
  fseek(fd, 0, SEEK_SET);
  W32* buf = (W32*)malloc(count);
  assert(fread(buf, count, 1, fd) == 1);
  fclose(fd);

  W32 startinsn = (argc > 2) ? (W32)(atoi(argv[2]) / 4) : 0;

  count /= 4;
  printf("Found %d instructions, buffer at 0x%08x\n", count, buf);
  printf("Starting at offset 0x%08x (insn 0x%08x)\n", startinsn*4, startinsn);

  byte* branch_target_map = new byte[count/2];
  memset(branch_target_map, 0, count/2);

	W32* p;
  W32 ip;

  //
  // Find branch targets
  //
  p = &buf[startinsn];
  ip = 0;

  while ((p < &buf[count])) {
    if (ip < CODE_SEG_START) {
      p += 4;
      ip += 16;
      continue;
    }
    if (ip >= DATA_SEG_START) {
      break;
    }

    W64 insn = *(W64*)p;
    int type = bits(insn, 61, 2);
    int commit = bit(insn, 63);

    switch (type) {
		case 0: {
      p += 4;
      ip += 16;
      if (commit) {
        Insn brinsn = (Insn)lo32(insn);
        W32 branch_target = brinsn.br.offset << 3;
        if ((branch_target>>3) < (count/2)) branch_target_map[branch_target>>3] = 1;
      }
      break;
    }
    case 1: { // LSU|ALU1
      p += 2; ip += 8; break;
    }
    case 2: { // ALU0|ALU1
      p += 2; ip += 8; break;
    }
    case 3: { // ALU0|BRU
      Insn brinsn = (Insn)lo32(insn);
      W32 branch_target = brinsn.br.offset << 3;
      if ((branch_target>>3) < (count/2)) branch_target_map[branch_target>>3] = 1;
      p += 2; ip += 8;
      break;
    }
    }
  }

  //
  // Print the instructions
  //
  p = &buf[startinsn];
  ip = 0;
  while (p < &buf[count]) {
    if (ip < CODE_SEG_START) {
      p += 4;
      ip += 16;
      continue;
    }

    if (ip >= DATA_SEG_START) {
      break;
    }

    W64 insn = *(W64*)p;
    int type = bits(insn, 61, 2);
    int commit = bit(insn, 63);

    if (branch_target_map[(ip >> 3)]) {
      printf("#=> target 0x%08x:\n", ip);
    }

    printf("0x%08x:\n", ip);

    alu0_used = false;
    alu1_used = false;
    lsu_used = false;
    bru_used = false;

    switch (type) {
		case 0: {
      W64 insn2 = *((W64*)&p[2]);
      p += 4;
      ip += 16;
      print_lsu_insn(hi32(insn2));
      print_alu1_insn(lo32(insn2));
      print_alu0_insn(hi32(insn), lo32(insn));
      if (commit) {
        print_bru_insn(lo32(insn));
        bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1_ALU0_BRU]++;
      } else {
        printf("  imm  0x%08x\n", lo32(insn));
        bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1_ALU0_IMM32]++;
      }
      if (bit(hi32(insn2), 31)) printf("  commit\n");
      break;
    }
    case 1: { // LSU|ALU1
      Insn insn0 = (Insn)hi32(insn); // (alu0 insn)
      Insn insn1 = (Insn)lo32(insn);
      print_lsu_insn(insn0);
      print_alu1_insn(insn1);
      bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1]++;
      if (commit) printf("  commit\n");
      p += 2; ip += 8;
      break;
    }
    case 2: { // ALU0|ALU1 or ALU0+imm32
      Insn insn0 = (Insn)hi32(insn); // (alu0 insn)
      Insn insn1 = (Insn)lo32(insn); // (alu1 insn)
      bool has_imm32 = op_uses_imm32(insn0.alu.op, 0);
      if (has_imm32) {
        print_alu0_insn(insn0, insn1.imm);
        printf("  imm  0x%08x\n", insn1.imm);
        bundle_type_histogram[BUNDLE_TYPE_ALU0_IMM32]++;
      } else {
        print_alu0_insn(insn0);
        print_alu1_insn(insn1);
        bundle_type_histogram[BUNDLE_TYPE_ALU0_ALU1]++;
      }
      if (commit) printf("  commit\n");
      p += 2; ip += 8;
      break;
    }
    case 3: { // ALU0|BRU
      Insn insn0 = (Insn)hi32(insn); // (alu0 insn)
      Insn insn1 = (Insn)lo32(insn);
      print_alu0_insn(insn0);
      print_bru_insn(insn1);
      bundle_type_histogram[BUNDLE_TYPE_ALU0_BRU]++;
      p += 2; ip += 8;
      if (commit) printf("  commit\n");
      break;
    }
    }

    if (lsu_used) {
      lsu_insns_in_a_row++;
      if (lsu_insns_in_a_row >= 32) {
        printf("# %d LSU insns in sequence\n", lsu_insns_in_a_row);
      }
    } else {
      lsu_insns_in_a_row = 0;
    }

    if (bru_used) {
      if (bru_insns_in_a_row == 0)
        saved_bru_insn_cond = last_bru_insn_cond;

      if (last_bru_insn_cond == saved_bru_insn_cond) {
        bru_insns_in_a_row++;
        if (bru_insns_in_a_row >= 2) {
          printf("# %d BRU insns in sequence\n", bru_insns_in_a_row);
        }
      } else {
        bru_insns_in_a_row = 0;
      }
    } else {
      bru_insns_in_a_row = 0;
    }

	}

  printf("\n");
  printf("Total instructions:  %15d\n", total_insns);
  printf("Total nops:          %15d\n", total_nops);
  printf("\n");
  printf("Bundle type histogram:\n");
  printf("LSU|ALU1|ALU0|imm32: %15d\n", bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1_ALU0_IMM32]);
  printf("LSU|ALU1|ALU0|BRU:   %15d\n", bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1_ALU0_BRU]);
  printf("LSU|ALU1:            %15d\n", bundle_type_histogram[BUNDLE_TYPE_LSU_ALU1]);
  printf("ALU0|imm32:          %15d\n", bundle_type_histogram[BUNDLE_TYPE_ALU0_IMM32]);
  printf("ALU0|ALU1:           %15d\n", bundle_type_histogram[BUNDLE_TYPE_ALU0_ALU1]);
  printf("ALU0|BRU:            %15d\n", bundle_type_histogram[BUNDLE_TYPE_ALU0_BRU]);

  print_opcode_histogram("Opcode histogram for ALU0", opcode_histogram_alu0);
  print_opcode_histogram("Opcode histogram for ALU1, type 0", opcode_histogram_alu1[0]);
  print_opcode_histogram("Opcode histogram for ALU1, type 1", opcode_histogram_alu1[1]);
  print_opcode_histogram("Opcode histogram for ALU1, type 2", opcode_histogram_alu1[2]);
  print_opcode_histogram("Opcode histogram for ALU1, type 3", opcode_histogram_alu1[3]);
  print_opcode_histogram("Opcode histogram for ALU1, type 4", opcode_histogram_alu1[4]);
  print_opcode_histogram("Opcode histogram for ALU1, type 5", opcode_histogram_alu1[5]);
  print_opcode_histogram("Opcode histogram for ALU1, type 6", opcode_histogram_alu1[6]);
  print_opcode_histogram("Opcode histogram for ALU1, type 7", opcode_histogram_alu1[7]);
  print_opcode_histogram("Opcode histogram for LSU", opcode_histogram_lsu);
}