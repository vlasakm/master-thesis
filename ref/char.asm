	default rel

	section .data
$str0:
	db	`%s\n`,0
$str1:
	db	`ok`,0
$str2:
	db	`not ok`,0
$str3:
	db	`\n`,0

	section .bss

	section .text


	extern printf

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 48
	mov rsp, rbp
	pop rbp
	ret

	global check
check:
.L0:
	push rbp
	mov rbp, rsp
	test rdi, rdi ; WO
	jnz .L1 ; R
	lea rsi, [$str2]
	jmp .L3
.L1:
	lea rsi, [$str1]
.L3:
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
	call f
	xor rdi, rdi ; W
	cmp rax, 48 ; WO
	setz dil ; R
	call check
	mov rax, 10
	xor rdi, rdi ; W
	cmp rax, 10 ; WO
	setz dil ; R
	call check
	mov rax, 13
	xor rdi, rdi ; W
	cmp rax, 13 ; WO
	setz dil ; R
	call check
	movsx rax, byte [$str3]
	xor rdi, rdi ; W
	cmp rax, 10 ; WO
	setz dil ; R
	call check
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
