	default rel

	section .data
$str0:
	db	`abcd`,0

	section .bss

	section .text


	extern memcpy

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
	movsx rax, byte [$str0]
	mov rsp, rbp
	pop rbp
	ret
.L3:
	movsx rcx, byte [rax]
	add rcx, 1 ; W
	mov byte [rax], cl
	lea rax, [rax+1]
	jmp .L2
