	default rel

	section .data
$str0:
	db	`%ld, `,0
$str1:
	db	`\n`,0

	section .bss
tmp:
	resb	40

	section .text


	extern memcpy

	extern printf

	global print_arr
print_arr:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-16], rbx
	mov [rbp-8], r12
	mov r12, rdi
	xor rbx, rbx ; W
.L2:
	cmp rbx, 5 ; WO
	jl .L3 ; R
	lea rdi, [$str1]
	call printf wrt ..plt
	mov rbx, [rbp-16]
	mov r12, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
.L3:
	mov rsi, [r12+8*rbx]
	lea rdi, [$str0]
	call printf wrt ..plt
	lea rbx, [rbx+1]
	jmp .L2

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 128 ; W
	xor rcx, rcx ; W
.L2:
	cmp rcx, 5 ; WO
	jl .L3 ; R
	lea rdi, [tmp]
	lea rsi, [rbp-120]
	mov rdx, 40
	call memcpy wrt ..plt
	lea rdi, [rbp-120]
	lea rsi, [rbp-80]
	mov rdx, 40
	call memcpy wrt ..plt
	lea rdi, [rbp-80]
	lea rsi, [tmp]
	mov rdx, 40
	call memcpy wrt ..plt
	lea rdi, [rbp-40]
	call print_arr
	lea rdi, [rbp-80]
	call print_arr
	lea rdi, [rbp-120]
	call print_arr
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
.L3:
	mov [rbp+8*rcx-40], rcx
	lea rdx, [rbp-80]
	mov rax, rcx
	lea rax, [rax+rax]
	mov [rdx+8*rcx], rax
	lea rdx, [rbp-120]
	mov rax, rcx
	lea rax, [rax+2*rax]
	mov [rdx+8*rcx], rax
	lea rcx, [rcx+1]
	jmp .L2
