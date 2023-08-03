	default rel

	section .data
$str0:
	db	`%ld %ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global fn1
fn1:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+1]
	mov rsp, rbp
	pop rbp
	ret

	global fn2
fn2:
.L0:
	push rbp
	mov rbp, rsp
	lea rax, [rdi+2]
	mov rsp, rbp
	pop rbp
	ret

	global select
select:
.L0:
	push rbp
	mov rbp, rsp
	test rdi, rdi ; WO
	cmovnz rdx, rsi
	mov rax, rdx
	mov rsp, rbp
	pop rbp
	ret

	global call1
call1:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rdi, rsi
	call rax
	mov rsp, rbp
	pop rbp
	ret

	global call2
call2:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rdi, rsi
	call rax
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 16 ; W
	mov [rbp-8], rbx
	lea rsi, [fn1]
	lea rdx, [fn2]
	xor rdi, rdi ; W
	call select
	mov rdi, rax
	mov rsi, 1
	call call1
	mov rbx, rax
	lea rsi, [fn1]
	lea rdx, [fn2]
	mov rdi, 1
	call select
	mov rdi, rax
	mov rsi, 1
	call call2
	mov rdx, rax
	lea rdi, [$str0]
	mov rsi, rbx
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rbx, [rbp-8]
	mov rsp, rbp
	pop rbp
	ret
