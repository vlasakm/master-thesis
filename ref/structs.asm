	default rel

	section .data
G:
	dq	5
$str0:
	db	`%ld\n`,0

	section .bss
H:
	resb	8
a:
	resb	16

	section .text


	extern memcpy

	extern printf

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, 1
	mov rsp, rbp
	pop rbp
	ret

	global global_offset
global_offset:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, [a+8]
	mov rsp, rbp
	pop rbp
	ret

	global global_offset2
global_offset2:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, [a+8]
	mov rsp, rbp
	pop rbp
	ret

	global local_offset
local_offset:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 32 ; W
	mov rax, [rbp-32]
	mov [rbp-16], rax
	mov rsp, rbp
	pop rbp
	ret

	global test
test:
.L0:
	push rbp
	mov rbp, rsp
	sub rsp, 32 ; W
	mov qword [rbp-8], 3
	mov qword [rbp-24], 5
	call f
	mov rcx, [G]
	add rcx, rax ; W
	mov rax, rcx
	add rax, [H] ; W
	add rax, [rbp-24] ; W
	mov [G], rax
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	call test
	mov rsi, [G]
	lea rdi, [$str0]
	xor rax, rax ; W
	call printf wrt ..plt
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
