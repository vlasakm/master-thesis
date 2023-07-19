	default rel

	section .data

	section .bss

	section .text


	extern memcpy

	global one
one:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 1
	mov rsp, rbp
	pop rbp
	ret

	global fun
fun:
.L0:
	push rbp
	mov rbp, rsp
	xor rax, rax ; W
.L1:
	test rdi, rdi ; WO
	jg .L2 ; R
	mov rsp, rbp
	pop rbp
	ret
.L2:
	lea rax, [rax+1]
	sub rdi, 1 ; W
	jmp .L1

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-8], rbx
	call one
	mov rbx, rax
	imul rbx, 20 ; W
	mov rdi, 10
	call fun
	lea rbx, [rbx+rax]
	call one
	lea rbx, [rbx+rax]
	mov rdi, 10
	call fun
	lea rbx, [rbx+rax]
	call one
	lea rax, [rbx+rax]
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
