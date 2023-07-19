	default rel

	section .data

	section .bss

	section .text


	extern memcpy

	global f
f:
.L0:
	push rbp
	mov rbp, rsp
	cmp rdi, 1 ; WO
	jz .L18 ; R
	cmp rdi, 2 ; WO
	jz .L17 ; R
	cmp rdi, 3 ; WO
	jz .L20 ; R
	cmp rdi, 4 ; WO
	jz .L21 ; R
	cmp rdi, 5 ; WO
	jz .L13 ; R
	cmp rdi, 6 ; WO
	jnz .L7 ; R
	xor rax, rax ; W
	jmp .L3
.L13:
	mov rax, 4
	jmp .L3
.L21:
	xor rax, rax ; W
	jmp .L3
.L20:
	xor rax, rax ; W
	jmp .L9
.L17:
	jmp .L7
.L18:
.L7:
	mov rax, 1
.L9:
	lea rax, [rax+2]
.L3:
	mov rsp, rbp
	pop rbp
	ret

	global main
main:
.L0:
	push rbp
	mov rbp, rsp
	xor rdi, rdi ; W
	call f
	mov rdi, 1
	call f
	mov rdi, 2
	call f
	mov rdi, 3
	call f
	mov rdi, 4
	call f
	mov rdi, 5
	call f
	mov rdi, 6
	call f
	mov rdi, 7
	call f
	xor rax, rax ; W
	mov rsp, rbp
	pop rbp
	ret
