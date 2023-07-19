	default rel

	section .data

	section .bss

	section .text


	extern memcpy

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	test rdi, rdi ; WO
	jnz .L2 ; R
	mov rax, 3
	jmp .L4
.L2:
	mov rax, 4
.L4:
	mov rsp, rbp
	pop rbp
	ret

	global g
g:
.L0:
	push rbp
	mov rbp, rsp
	test rdi, rdi ; WO
	jnz .L2 ; R
	mov rax, 3
	jmp .L5
.L2:
	mov rax, 4
.L5:
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-8], rbx
	mov rdi, 1
	call f
	mov rbx, rax
	xor rdi, rdi ; W
	call g
	lea rax, [rbx+rax]
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
