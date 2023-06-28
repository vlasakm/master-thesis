	default rel

	section .data

	section .bss

	section .text


	global f1
f1:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+8*rsi]
	mov rsp, rbp
	pop rbp
	ret

	global f2
f2:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+8*rsi]
	mov rsp, rbp
	pop rbp
	ret

	global f3
f3:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rcx, 1
	imul rcx, rcx, 8 ; W
	mov rsp, rbp
	pop rbp
	ret

	global f4
f4:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+8]
	mov rsp, rbp
	pop rbp
	ret

	global g1
g1:
.L0:
	push rbp
	mov rbp, rsp
	neg rsi ; W
	lea rax, [rdi+8*rsi]
	mov rsp, rbp
	pop rbp
	ret

	global g2
g2:
.L0:
	push rbp
	mov rbp, rsp
	neg rsi ; W
	lea rax, [rdi+8*rsi]
	mov rsp, rbp
	pop rbp
	ret

	global g3
g3:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rcx, -1
	imul rcx, rcx, 8 ; W
	mov rsp, rbp
	pop rbp
	ret

	global g4
g4:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi-8]
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
