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

	global sll
sll:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rcx, rsi
	shl rax, cl
	mov rsp, rbp
	pop rbp
	ret

	global sar
sar:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rcx, rsi
	sar rax, cl
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 1
	xor rsi, rsi ; W
	call sll
	mov rsi, rax
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, 1
	mov rsi, 1
	call sll
	mov rsi, rax
	lea rdi, [$str1]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, 1
	mov rsi, 10
	call sll
	mov rsi, rax
	lea rdi, [$str2]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, 1
	xor rsi, rsi ; W
	call sar
	mov rsi, rax
	lea rdi, [$str3]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, 1
	mov rsi, 1
	call sar
	mov rsi, rax
	lea rdi, [$str4]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, -1
	mov rsi, 10
	call sar
	mov rsi, rax
	lea rdi, [$str5]
	xor rax, rax ; W
	call printf wrt ..plt
	mov rdi, -128
	mov rsi, 4
	call sar
	mov rsi, rax
	lea rdi, [$str6]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
