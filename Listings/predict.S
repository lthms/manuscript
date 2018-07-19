movq $0,%rax
loop:
  incq %rax
  cmp $10,%rax
  jle loop
movq $0,%rax
