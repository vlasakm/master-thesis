	default rel

	section .data

	section .bss

	section .text


	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 10
	mov rsp, rbp
	pop rbp
	ret
