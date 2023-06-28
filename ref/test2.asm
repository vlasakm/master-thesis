	default rel

	section .data

	section .bss

	section .text


	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rcx, 2
	mov rax, 10
	cqo
	idiv rcx
	lea rax, [rax+4]
	mov rsp, rbp
	pop rbp
	ret
