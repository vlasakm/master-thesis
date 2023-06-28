	default rel

	section .data
$str0:
	db	`%ld %ld\n`,0

	section .bss

	section .text


	extern printf

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 32 ; W
	mov qword [rbp-16], 2
	mov qword [rbp-8], 3
	mov rax, [rbp-16]
	mov [rbp-32], rax
	mov rax, [rbp-8]
	mov [rbp-24], rax
	mov rsi, [rbp-32]
	mov rdx, [rbp-24]
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
