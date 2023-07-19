	default rel

	section .data
$str0:
	db	`%ld\n`,0

	section .bss

	section .text


	extern memcpy

	extern printf

	global mul1
mul1:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	mov rsp, rbp
	pop rbp
	ret

	global mul2
mul2:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	lea rax, [rax+rax]
	mov rsp, rbp
	pop rbp
	ret

	global mul3
mul3:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	lea rax, [rax+2*rax]
	mov rsp, rbp
	pop rbp
	ret

	global mul4
mul4:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	shl rax, 2 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul5
mul5:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	lea rax, [rax+4*rax]
	mov rsp, rbp
	pop rbp
	ret

	global mul6
mul6:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	imul rax, 6 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul7
mul7:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	imul rax, 7 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul8
mul8:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	shl rax, 3 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul9
mul9:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	lea rax, [rax+8*rax]
	mov rsp, rbp
	pop rbp
	ret

	global mul10
mul10:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	imul rax, 10 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul16
mul16:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	shl rax, 4 ; W
	mov rsp, rbp
	pop rbp
	ret

	global mul32
mul32:
.L0:
	push rbp
	mov rbp, rsp
	mov rax, rdi
	shl rax, 5 ; W
	mov rsp, rbp
	pop rbp
	ret

	global print
print:
.L0:
	push rbp
	mov rbp, rsp
	mov rsi, rdi
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
	mov rdi, 15
	call mul1
	mov rdi, rax
	call print
	mov rdi, 30
	call mul2
	mov rdi, rax
	call print
	mov rdi, -20
	call mul3
	mov rdi, rax
	call print
	mov rdi, 1
	call mul4
	mov rdi, rax
	call print
	mov rdi, 8
	call mul5
	mov rdi, rax
	call print
	mov rdi, 4294967296
	call mul6
	mov rdi, rax
	call print
	mov rdi, 25
	call mul7
	mov rdi, rax
	call print
	mov rdi, 9
	call mul8
	mov rdi, rax
	call print
	mov rdi, 10
	call mul9
	mov rdi, rax
	call print
	mov rdi, -50
	call mul10
	mov rdi, rax
	call print
	mov rdi, 25
	call mul16
	mov rdi, rax
	call print
	mov rdi, 4
	call mul32
	mov rdi, rax
	call print
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
