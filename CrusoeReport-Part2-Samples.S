#
# Handler for reading MSR registers from x86 operating system code.
# Illustrates the code for functionality well documented in published
# specifications from Transmeta.
#
read_msr:
#=> target 0x000a6798:
0x000a6798:
  ALU0 5039aff4 = 010 100000011 100110 101111 11110100
  ALU1 103befe0 = 000 100000011 101111 101111 11100000
  # addi    %r38,%r47,-12        # %r38 = %sp - 12
  # addi    %r47,%r47,-32        # %sp = %sp - 32
0x000a67a0:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 1038e604 = 000 100000011 100011 100110 00000100
  ALU0 1bb8bf00 = 000 110111011 100010 111111 00000000
  imm  0x80000000
  # nop.lsu  
  # addi    %r35,%r38,4          # %r35 = %r38 + 4
  # oril    %r34,%zero,0x80000000 # %r34 = 0x80000000
0x000a67b0:
  LSU  044319bf = 000 001000100 001100 011001 10111111
  ALU1 100f008b = 000 100000000 111100 000000 10001011
  nop0 14b00000 = 000 101001011 000000 000000 00000000
  imm  0x14b00000                                     
  # st      [%r47],%r25          # Save %r25
  # add     %r60,%r0,%r34        # %r60 = %r0 (%eax) + 0x80000000
  #                              # (to bring MSR offset down to zero base)
0x000a67c0:
  LSU  04431a8f = 000 001000100 001100 011010 10001111
  ALU1 09397c04 = 000 010010011 100101 111100 00000100
  ALU0 18367f00 = 000 110000011 011001 111111 00000000
  imm  0x0018aae0
  # st      [%r35],%r26          # Save %r26
  # slli    %r37,%r60,4          # Shift MSR number for indexing into table
  # addil   %r25,%zero,0x0018aae0
  #                              # 0x18aae0 -> cpuid data for 0x80000000-6
  # NOTE: shifts (slli, etc.) appear to only be available on ALU1, at least
  # according to the opcode map. This is a bizarre (but low power) design.
0x000a67d0:
  LSU  04431b9b = 000 001000100 001100 011011 10011011
  ALU1 4606fa03 = 010 001100000 011011 111010 00000011
  ALU0 1f3f8000 = 000 111110011 111110 000000 00000000
  imm  0x80000006
  # st      [%r38],%r27          # [%sp-12] = %r27 (callee saved)
  # 001100000 %r27,%r58,%r0      # 
  # cmpil.c %sink,%r0,0x80000006 # compare %eax == 0x80000006?
0x000a67e0:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 103ed9c0 = 000 100000011 111011 011001 11000000
  ALU0 18392500 = 000 110000011 100100 100101 00000000
  imm  0x0018aae0
  # nop.lsu
  # addi    %r59,%r25,-64        # 0x18aaa0 -> cpuid data returned for 0x0-0x3
  # addil   %r36,%r37,0x0018aae0 # %r36 = 0x18aae0 + (%r60 << 4)
0x000a67f0:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 170f808b = 000 101110000 111110 000000 10001011
  ALU0 9386bfff = 100 100111000 011010 111111 11111111
  BRU  ae014d0c = 101 0111 0  000000010100110100001100
  # nop.lsu
  # cmp.c   %sink,%r0,%r34       # compare %eax == 0x80000000
  # or      %r26,%zero,%zero     # Move %r26 = 0
  # br.gt   0x000a6860           # branch if %eax > 0x80000006
  #                              # (to handle 0x80860000 functions)
0x000a6800:
  ALU0 773f8003 = 011 101110011 111110 000000 00000011
  BRU  a6014d17 = 101 0011 0  000000010100110100010111
  # cmp.c   %sink,%r0,3          # Compare %eax == 3
  # br.ge   0x000a68b8           # branch if (%eax >= 0x80000000)
  # (branch to load_cpuid_data_to_regs)
0x000a6808:
  ALU0 538f00ff = 010 100111000 111100 000000 11111111
  ALU1 09394004 = 000 010010011 100101 000000 00000100
  # or      %r60,%r0,%zero       # %r60 = %eax
  # slli    %r37,%r0,4           # %r37 = %eax << 4 (index cpuid table)
0x000a6810:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 100925ef = 000 100000000 100100 100101 11101111
  ALU0 93867bff = 100 100111000 011001 111011 11111111
  # nop.lsu
  # add     %r36,%r37,%r59       # %r36 = %r37 + (%r0<<4) + 0x18aaa0
#=> target 0x000a6820:
0x000a6820:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 1038ef14 = 000 100000011 100011 101111 00010100
  ALU0 1380bfff = 000 100111000 000010 111111 11111111
  imm  0x14b00000
  # nop.lsu
  # addi    %r35,%r47,20         # %r35 = %r47 + 20
  # or      %r2,%zero,%zero      # %edx = 0
0x000a6830:
  ALU0 53807fff = 010 100111000 000001 111111 11111111
  ALU1 1380ffff = 000 100111000 000011 111111 11111111
  # move    %r1,%zero,%zero        # %ecx = 0 
  # move    %r3,%zero,%zero        # %ebx = 0
0x000a6838:
  ALU0 53803fff = 010 100111000 000000 111111 11111111
  ALU1 1038af18 = 000 100000011 100010 101111 00011000
  # move    %r0,%zero,%zero        # Set %eax = 0
  # addi    %r34,%r47,24           # %r34 = %sp + 24
#=> target 0x000a6840:
0x000a6840:
  LSU  2506c48f = 001 001010000 011011 000100 10001111
  ALU1 46803a6f = 010 001101000 000000 111010 01101111
  # ld      %r27,[%r35]       # load %r27 = [%r35]
  # br.prep %r0,%r58,%r27     # prepare branch (%r58 = %link)
0x000a6848:
  LSU  2506848b = 001 001010000 011010 000100 10001011
  nop1 14b00000 = 000 101001011 000000 000000 00000000
  # ld      %r26,[%r34]       # restore saved register
  # nop
0x000a6850:
  LSU  050644bf = 000 001010000 011001 000100 1011111
  ALU1 103bef20 = 000 100000011 101111 101111 0010000
  nop0 94b00000 = 100 101001011 000000 000000 00000000
  BRU  80800076 = 100 0000 0 10000000000000000111011 0
  # ld      %r25,[%r47]       # restore saved register
  # addi    %r47,%r47,32      # restore stack frame
  # nop
  # br.ret  %r58              # return to caller (%r58 = %from)

#
# Load %eax/%ebx/%ecx/%edx with values for a given cpuid
# MSR read request. Illustrates operation of load unit.
#

load_cpuid_data_to_regs:
#=> target 0x000a68b8:
0x000a68b8:
  nop0 54b00000 = 010 101001011 000000 000000 00000000
  nop1 14b00000 = 000 101001011 000000 000000 00000000
0x000a68c0:
  ALU0 5039e40c = 010 100000011 100111 100100 00001100
  ALU1 103a2404 = 000 100000011 101000 100100 00000100
  # addi    %r39,%r36,12         # %r39 = %r36 + 12   (0x18aaec -> "smet")
  # addi    %r40,%r36,4          # %r40 = %r36 + 4    (0x18aae4 -> "Tran")
0x000a68c8:
  LSU  25000493 = 001 001010000 000000 000100 10010011
  ALU1 1039a408 =<000>100000011 100110 100100 00001000
  # ld      %r0,[%r36]           # %eax = max cpuid request id
  # addi    %r38,%r36,8          # %r38 = %r38 + 8 (= 0x18aae8)
0x000a68d0:
  LSU  2500c4a3 = 001 001010000 000011 000100 10100011
  ALU1 170f9aff = 000 101110000 111110 011010 11111111
  # ld      %r3,4,[%r40]         # load %ebx (%r3) = "Tran"
  # cmp.c   %sink,%r26,%zero     # (as called from above, %r26 always is zero)
0x000a68d8:
  LSU  2500849f = 001 001010000 000010 000100 10011111
  ALU1 1038ef14 = 000 100000011 100011 101111 00010100
  # ld      %r2,[%r39]           # load %edx (%r2) = "smet"
  # addi    %r35,%r47,20         # r35 = r47 + 20
0x000a68e0:
  LSU  0500449b = 000 001010000 000001 000100 10011011
  ALU1 1038af18 = 000 100000011 100010 101111 00011000
  nop0 94b00000 = 100 101001011 000000 000000 00000000
  BRU  a8014d08 = 101 01000 00000001 01001101 00001000
  # ld      %r1,[%r38]           # load %ecx (%r1) = "aCPU" (%r38 = 0x18aae8)
  # addi    %r34,%r47,24         # %r34 = %r47 + 24
  # nop
  # br.eq   0x000a6840           # branch to common completion
0x000a68f0:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  nop1 74b00014 = 011 101001011 000000 000000 00010100
  nop0 14b00000 = 000 101001011 000000 000000 00000000
  imm  0x14b00000
  # nop.lsu | nop | nop | nop
0x000a6900:
  nop0 54b00000 = 010 101001011 000000 000000 00000000
  nop1 74b00315 = 011 101001011 000000 000011 00010101
0x000a6908:
  nop0 54b00000 = 010 101001011 000000 000000 00000000
  nop1 74b00116 = 011 101001011 000000 000001 00010110
0x000a6910:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  nop1 74b00217 = 011 101001011 000000 000010 00010111
  nop0 94b00000 = 100 101001011 000000 000000 00000000
  BRU  80014d08 = 100 00000 00000001 01001101 00001000
  # nop.lsu | nop | nop
  # br      0x000a6840 

#
# Called to enable/disable processor serial number (PSN)
# when bit 21 of MSR 0x119 is written. Top level write_msr
# handler is not shown, but is similar to read_msr.
#
# On entry:
#
# %r37 -> cpu_feature_flags (at 0x0018aabc)
# %r38 -> current value of msr_psn_disable
#

#=> target 0x000a6f20:
0x000a6f20:
  LSU  050a8497 = 000 001010000 101010 000100 10010111
  ALU1 170f80ff = 000 101110000 111110 000000 11111111
  ALU0 1a3b0000 = 000 110100011 101100 000000 00000000
  imm  0xffdfffff
  # ld      %r42,%r4,%r37/3      # %r42 = [%r37] (load cpuid feature flags)
  # cmp.c   %sink,%r0,%zero      # is %eax zero? (%eax = 0) meaning: *enable* PSN
  # andil   %r44,%r0,0xffdfffff  # %r44 = %eax & ~(1<<21): bit21 = PSN disable bit
0x000a6f30:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 020342ff = 000 000100000 001101 000010 11111111
  ALU0 1a3a6a00 = 000 110100011 101001 101010 00000000
  imm  0xfffbffff
  # nop.lsu
  # cmp.and %r13,%r2,%zero       # %edx == %zero (high 32 bits in %edx must be zero)
  # andil   %r41,%r42,0xfffbffff # 0xfffbffff = ~(1 << 18) = PSN feature flag
0x000a6f40:
  LSU  03b00600 = 000 000111011 000000 000110 00000000
  ALU1 1388e5ff = 000 100111000 100011 100101 11111111
  ALU0 82036cff = 100 000100000 001101 101100 11111111
  BRU  a8014dc9 = 101 0100 0 000000010100110111001001
  # nop.lsu
  # or      %r35,%r37,%zero      # %r35 = %r37
  # cmp.and %r13,%r44,%zero      # cmp.and %r44 == %zero
  #                              # (i.e., no other bits are set in %eax)
  # br.eq   0x000a6e48           # (if %eax = 0 [means "enable PSN"], branch)
0x000a6f50:
  LSU  04432997 = 000 001000100 001100 101001 10010111
  ALU1 13b9ff01 = 000 100111011 100111 111111 00000001
  ALU0 103a25e4 = 000 100000011 101000 100101 11100100
  imm  0x14b00000
  # st      [%r37],%r41          # cpu_feature_flags &= PSN_FF_BIT
  # ori     %r39,%zero,1         # %r39 = 1
  # addi    %r40,%r37,-28        # %r40 = 0x0018aaa0 [0x3 'Genu' 'Mx86' 'ineT']
0x000a6f60:
  LSU  0443009b = 000 001000100 001100 000000 10011011
  ALU1 10396518 = 000 100000011 100101 100101 00011000
  ALU0 1039a514 = 000 100000011 100110 100101 00010100
  imm  0x14b00000
  # st      [%r38],%r0           # st [%r38],%r0 (%eax => msr_psn_disable)
  # addi    %r37,%r37,24         # %r37 = 0x18aad4 &("my unique id")
  # addi    %r38,%r37,20         # %r38 = 0x18aad0 &(before "my unique id")
0x000a6f70:
  LSU  044327a3 = 000 001000100 001100 100111 10100011
  nop1 14b00000 = 000 101001011 000000 000000 00000000
  nop0 14b00000 = 000 101001011 000000 000000 00000000
  imm  0x14b00000
  # st      [%r40],%r39          # max_cpuid_base_func_number = %r39 (i.e., 1)
0x000a6f80:
  LSU  24433f97 = 001 001000100 001100 111111 10010111
  ALU1 1038a320 = 000 100000011 100010 100011 00100000
  # st      [%r37],%zero         # ["my u"] = 0
  # addi    %r34,%r35,32         # %r34 = 0x18aadc
0x000a6f88:
  LSU  24433f9b = 001 001000100 001100 111111 10011011
  ALU1 1039231c = 000 100000011 100100 100011 00011100
  # st      [%r38],%zero         # [word before "my unique id"] = 0
  # addi    %r36,%r35,28         # %r36 = 0x18aad8
0x000a6f90:
  LSU  24433f8b = 001 001000100 001100 111111 10001011
  nop1 14b00000 = 000 101001011 000000 000000 00000000
  # st      [%r34],%zero         # ["e ID"] = 0
0x000a6f98:
  LSU  24433f93 = 001 001000100 001100 111111 10010011
  nop1 14b00000 = 000 101001011 000000 000000 00000000
  # st      [%r36],%zero         # ["niqu"] = 0
0x000a6fa0: 
  nop0 54b00000 = 010 101001011 000000 000000 00000000
  nop1 14b00000 = 000 101001011 000000 000000 00000000
0x000a6fa8:
  nop0 74b00000 = 011 101001011 000000 000000 00000000
  BRU  80014dc9 = 100 0000 0 000000010100110111001001
  # br      0x000a6e48
