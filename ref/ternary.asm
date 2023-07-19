	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global print_res
print_res:
.L0:
	push rbp
	mov rbp, rsp
	mov rsi, rdi
	lea rdi, [$str0]
	call printf wrt ..plt
	mov rsp, rbp
	pop rbp
	ret

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
	mov rdi, rax
	call print_res
	xor rdi, rdi ; W
	mov rsi, 2
	mov rdx, 3
	call f
	mov rdi, rax
	call print_res
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
