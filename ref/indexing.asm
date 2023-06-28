	default rel

	section .data

	section .bss

	section .text


	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, [rdi+8*rsi]
	add rax, [rdi+8*rdx] ; W
	mov [rdi+8*rcx], rax
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 10
	mov rsp, rbp
	pop rbp
	ret
