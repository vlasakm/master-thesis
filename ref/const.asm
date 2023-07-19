	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global add1
add1:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+2147483647]
	mov rsp, rbp
	pop rbp
	ret

	global add2
add2:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi-2147483648]
	mov rsp, rbp
	pop rbp
	ret

	global add3
add3:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	sub rax, -2147483648 ; W
	mov rsp, rbp
	pop rbp
	ret

	global add4
add4:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	sub rax, -2147483647 ; W
	mov rsp, rbp
	pop rbp
	ret

	global print
print:
.L0:
	push rbp
	mov rbp, rsp
	mov rsi, rdi
	lea rdi, [$str0]
	call printf wrt ..plt
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 10
	call add1
	mov rdi, rax
	call print
	mov rdi, 10
	call add2
	mov rdi, rax
	call print
	mov rdi, 10
	call add3
	mov rdi, rax
	call print
	mov rdi, 10
	call add4
	mov rdi, rax
	call print
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
