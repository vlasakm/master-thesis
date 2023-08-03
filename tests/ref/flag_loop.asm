	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-8], rbx
.L1:
	mov rbx, rdi
	sub rbx, 1 ; WO
	jg .L2 ; R
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
.L2:
	lea rdi, [$str0]
	mov rsi, rbx
	call printf wrt ..plt
	mov rdi, rbx
	jmp .L1

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 3
	call f
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
