	default rel

	section .data

	section .bss

	section .text


	extern memcpy

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rcx, 3
	mov rdx, -1
	mov rsi, 20
	xor rax, rax ; W
	cmp rcx, 3 ; WO
	jnz .L2 ; R
	mov rcx, -1
	xor rax, rax ; W
	cmp rdx, rcx ; WO
	setz al ; R
.L2:
	test rax, rax ; WO
	jz .L4 ; R
	mov rcx, -20
	xor rax, rax ; W
	cmp rsi, rcx ; WO
	setz al ; R
.L4:
	mov rsp, rbp
	pop rbp
	ret
