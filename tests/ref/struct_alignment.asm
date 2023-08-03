	default rel

	section .data
$str0:
	db	`%ld %ld %ld\n`,0
$str1:
	db	`%ld %ld %ld %ld\n`,0

	section .bss
b:
	resb	24

	section .text


	extern memcpy

	extern printf

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 32 ; W
	mov qword [rbp-24], 5
	mov byte [rbp-16], 97
	mov qword [rbp-8], 3
	mov qword [b], 20
	mov byte [b+8], 98
	mov byte [b+9], 99
	mov qword [b+16], 21
	mov rsi, [rbp-24]
	movsx rdx, byte [rbp-16]
	mov rcx, [rbp-8]
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rsi, [b]
	movsx rdx, byte [b+8]
	movsx rcx, byte [b+9]
	mov r8, [b+16]
	lea rdi, [$str1]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
