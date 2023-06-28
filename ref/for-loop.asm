	default rel

	section .data

	section .bss

	section .text


	global add_one
add_one:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+1]
	mov rsp, rbp
	pop rbp
	ret

	global add_two
add_two:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+2]
	mov rsp, rbp
	pop rbp
	ret

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 48 ; W
	mov [rbp-48], rbx
	mov [rbp-40], r12
	mov [rbp-32], r13
	mov [rbp-24], r14
	mov [rbp-16], r15
	mov [rbp-8], rdi
	mov r15, rsi
	xor r12, r12 ; W
	xor r13, r13 ; W
	xor rbx, rbx ; W
.L2:
	cmp r12, 10 ; WO
	jl .L3 ; R
	lea rax, [r13+rbx]
	mov rbx, [rbp-8]
	add rax, rbx ; W
	lea rax, [rax+r15]
	mov rbx, [rbp-48]
	mov r12, [rbp-40]
	mov r13, [rbp-32]
	mov r14, [rbp-24]
	mov r15, [rbp-16]
	mov rsp, rbp
	pop rbp
	ret
.L3:
	xor r14, r14 ; W
.L7:
	cmp r14, 10 ; WO
	jl .L8 ; R
	mov rdi, rbx
	call add_two
	lea r12, [r12+1]
	mov rbx, rax
	jmp .L2
.L8:
	mov rdi, r13
	call add_one
	lea r14, [r14+1]
	mov r13, rax
	jmp .L7

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 3
	mov rsi, 4
	call f
	mov rsp, rbp
	pop rbp
	ret
