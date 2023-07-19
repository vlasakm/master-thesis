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
	cmovnz rdx, rsi
	mov rax, rdx
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 1
	mov rsi, 2
	mov rdx, 3
	call f
	xor rcx, rcx ; W
	cmp rax, 2 ; WO
	jnz .L2 ; R
	xor rdi, rdi ; W
	mov rsi, 2
	mov rdx, 3
	call f
	xor rcx, rcx ; W
	cmp rax, 3 ; WO
	setz cl ; R
.L2:
	mov rax, rcx
	mov rsp, rbp
	pop rbp
	ret
