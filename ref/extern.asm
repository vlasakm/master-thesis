	default rel

	section .data
$str0:
	db	`hello world %d\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	lea rdi, [$str0]
	mov rsi, 20
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
