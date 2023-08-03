	default rel

	section .data
$str0:
	db	`abcd`,0
$str1:
	db	`%s\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [$str0]
.L2:
	movsx rcx, byte [rax]
	test rcx, rcx ; WO
	jnz .L3 ; R
	lea rdi, [$str1]
	lea rsi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
.L3:
	movsx rcx, byte [rax]
	add rcx, 1 ; W
	mov byte [rax], cl
	lea rax, [rax+1]
	jmp .L2
