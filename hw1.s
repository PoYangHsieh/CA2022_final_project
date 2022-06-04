.data
    n: .word 11
.text
.globl __start

FUNCTION:
    addi sp,sp,-4
    sw x1,0(sp)
    # Todo: Define your own function in HW1
    BEGIN:
    addi x3,x0,1 #x3 is 1
    addi x24,x0,11 #x24 is 11
    jal x1,T
    
    lw x1,0(sp)
    addi sp,sp,4
    jalr x0,0(x1)
  
  T:
    addi sp,sp,-8
    sw x10,0(sp)
    sw x1,4(sp)
    
    bge x10,x24,T2
    bge x10,x3,T1
    
    addi x5,x0,7
    
    addi sp,sp,8
    jalr x0,0(x1)
  T1:
    addi x10,x10,-1
    jal x1,T
    
    lw x1,4(sp)
    lw x20,0(sp)
    addi sp,sp,8
    
    addi x4,x0,2
    mul x5,x5,x4
    
    jalr x0,0(x1)
  T2:
    addi x22,x0,3  #3/4
    mul x10,x10,x22
    srli x10,x10,2
    jal x1,T
    
    lw x1,4(sp)
    lw x20,0(sp)
    addi sp,sp,8
    
    addi x4,x0,2 #*2
    mul x5,x5,x4
    
    addi x23,x0,7 #0.875
    mul x21,x20,x23
    srli x21,x21,3
    
    add x5,x5,x21 #-137
    addi x5,x5,-137
    
    jalr x0,0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   a0, n
    sw   t0, 4(a0)
    addi a0,x0,10
    ecall