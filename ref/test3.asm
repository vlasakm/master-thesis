	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global test
test:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 10
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	call test
	mov rsi, rax
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
