.data
    n: .word 10 # You can change this number
    
.text
.globl __start

FUNCTION:
	# jump to t_base if a0 == 1
	li t1, 1
	beq a0, t1, F_base

  # keep variables
  addi sp, sp, -8
  sw ra, 4(sp)
  sw a0, 0(sp)

  # call T(n/2)
  srli a0, a0, 1
  jal ra, FUNCTION

  # restore variables
  lw t1, 0(sp)          # load n
  lw ra, 4(sp)
  addi sp, sp, 8

  # compute and return 4T(n/2)+2n
  slli t0, t0, 2
  slli t1, t1, 1
  add t0, t0, t1
  jalr x0, 0(ra)

F_base:
	# return 1
	addi t0, x0, 1
  jalr x0, 0(ra)
    

# Do not modify this part!!! #
__start:                     #
    la   t0, n               #
    lw   x10, 0(t0)          #
    jal  x1,FUNCTION         #
    la   t0, n               #
    sw   x10, 4(t0)          #
    addi a0,x0,10            #
    ecall                    #
##############################
