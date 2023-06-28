	default rel

	section .data
$str0:
	db	`%ld\n`,0
$str1:
	db	`%ld\n`,0
$str2:
	db	`%ld\n`,0
$str3:
	db	`%ld\n`,0
$str4:
	db	`%ld\n`,0
$str5:
	db	`%ld\n`,0
$str6:
	db	`%ld\n`,0

	section .bss

	section .text


	extern printf

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+rsi]
	cmp rax, 2 ; WO
	jle .L4 ; R
	mov rdi, 4
.L4:
	mov rax, rdi
	imul rax, rsi ; WO
	jnz .L10 ; R
	mov rdi, 1
.L10:
	mov rax, rdi
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 32 ; W
	mov [rbp-24], rbx
	mov [rbp-16], r12
	mov [rbp-8], r13
	mov rdi, 1
	mov rsi, 3
	call f
	mov r13, rax
	mov rdi, 1
	xor rsi, rsi ; W
	call f
	mov r12, rax
	mov rbx, 5
	xor rax, rax ; W
	test rbx, 5 ; WO
	setz al ; R
	xor rcx, rcx ; W
	cmp rax, 1 ; WO
	setnz cl ; R
	xor rbx, rbx ; W
	test rcx, rcx ; WO
	setz bl ; R
	lea rdi, [$str0]
	mov rsi, r13
	xor rax, rax ; W
	call printf wrt ..plt
	lea rdi, [$str1]
	mov rsi, r12
	xor rax, rax ; W
	call printf wrt ..plt
	lea rdi, [$str2]
	mov rsi, 5
	xor rax, rax ; W
	call printf wrt ..plt
	lea rdi, [$str3]
	mov rsi, rbx
	xor rax, rax ; W
	call printf wrt ..plt
	xor rsi, rsi ; W
	cmp r13, r12 ; WO
	setz sil ; R
	lea rdi, [$str4]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rsi, rsi ; W
	cmp r12, 5 ; WO
	setl sil ; R
	lea rdi, [$str5]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	cmp r13, r12 ; WO
	setz al ; R
	xor rbx, rbx ; W
	cmp r12, 5 ; WO
	setl bl ; R
	xor rsi, rsi ; W
	cmp rax, rbx ; WO
	setnz sil ; R
	lea rdi, [$str6]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rbx, [rbp-24]
	mov r12, [rbp-16]
	mov r13, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
