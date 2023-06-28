	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern printf

	global fn1
fn1:
.L0:
	push rbp
	mov rbp, rsp
	mov r10, [rbp+16]
	mov rax, [rbp+24]
	lea rsi, [rsi+rsi]
	lea rsi, [rdi+rsi]
	lea rdx, [rdx+2*rdx]
	lea rdx, [rsi+rdx]
	shl rcx, 2 ; W
	lea rcx, [rdx+rcx]
	lea r8, [r8+4*r8]
	lea rcx, [rcx+r8]
	imul r9, 6 ; W
	lea rcx, [rcx+r9]
	imul r10, 7 ; W
	lea rcx, [rcx+r10]
	shl rax, 3 ; W
	lea rax, [rcx+rax]
	mov rsp, rbp
	pop rbp
	ret

	global fn2
fn2:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-8], rbx
	mov r11, rdi
	mov r10, rsi
	mov rbx, rdx
	mov rax, rcx
	mov rdx, r9
	mov rsi, [rbp+16]
	mov rdi, [rbp+24]
	mov rcx, r8
	mov r8, rax
	mov r9, rbx
	push r11
	push r10
	call fn1
	add rsp, 16 ; W
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	mov rdi, 8
	mov rsi, 7
	mov rdx, 6
	mov rcx, 5
	mov r8, 4
	mov r9, 3
	push 1
	push 2
	call fn2
	add rsp, 16 ; W
	mov rsi, rax
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
