	default rel

	section .data
$str0:
	db	`%ld %ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

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
	mov rdx, rax
	lea rdi, [$str0]
	mov rsi, rbx
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
