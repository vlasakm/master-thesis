	default rel

	section .data
$str0:
	db	`%ld\n`,0
$str1:
	db	`%ld %ld %ld %ld %ld\n`,0

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
	sub rsp, 48 ; W
	mov qword [rbp-40], 0
	mov qword [rbp-32], 1
	lea rdi, [rbp-40]
	xor rsi, rsi ; W
	mov rdx, 1
	mov rcx, 2
	call f
	mov rdi, rax
	call print_res
	lea rdi, [rbp-40]
	mov rsi, 1
	mov rdx, 2
	mov rcx, 3
	call f
	mov rdi, rax
	call print_res
	lea rdi, [rbp-40]
	mov rsi, 2
	mov rdx, 3
	mov rcx, 4
	call f
	mov rdi, rax
	call print_res
	lea rax, [rbp-40]
	mov rsi, [rax]
	lea rax, [rbp-40]
	mov rdx, [rax+8]
	lea rax, [rbp-40]
	mov rcx, [rax+16]
	lea rax, [rbp-40]
	mov r8, [rax+24]
	lea rax, [rbp-40]
	mov r9, [rax+32]
	lea rdi, [$str1]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
