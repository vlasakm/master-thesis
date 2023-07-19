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
	mov rax, 21
	mov rsp, rbp
	pop rbp
	ret
