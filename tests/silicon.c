#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define STACK_BASE 0x10000000UL
#define STACK_SIZE 0x100000UL
#define STACK_TOP (STACK_BASE + STACK_SIZE / 2)
#define CODE_BASE 0x20000000UL
#define CODE_SIZE 0x20000UL
#define EXIT_STUB (CODE_BASE + 0x10000UL)
#define DUMP 128

uint64_t in_regs[16];
uint64_t out_regs[17];
uint64_t in_rsp;
uint64_t in_code;
uint64_t host_rsp;
extern void enter(void);
extern char leave_point[];
static sigjmp_buf rescue;

__asm__(
  ".intel_syntax noprefix\n"
  ".text\n"
  ".globl enter\n"
  "enter:\n"
  "push rbx\n"
  "push rbp\n"
  "push r12\n"
  "push r13\n"
  "push r14\n"
  "push r15\n"
  "mov [rip+host_rsp], rsp\n"
  "push qword ptr [rip+in_regs+120]\n"
  "popfq\n"
  "mov rsp, [rip+in_rsp]\n"
  "mov rcx, [rip+in_regs+8]\n"
  "mov rbx, [rip+in_regs+16]\n"
  "mov rdx, [rip+in_regs+24]\n"
  "mov r8, [rip+in_regs+32]\n"
  "mov r9, [rip+in_regs+40]\n"
  "mov rsi, [rip+in_regs+48]\n"
  "mov rdi, [rip+in_regs+56]\n"
  "mov rbp, [rip+in_regs+64]\n"
  "mov r10, [rip+in_regs+72]\n"
  "mov r11, [rip+in_regs+80]\n"
  "mov r12, [rip+in_regs+88]\n"
  "mov r13, [rip+in_regs+96]\n"
  "mov r14, [rip+in_regs+104]\n"
  "mov r15, [rip+in_regs+112]\n"
  "mov rax, [rip+in_regs+0]\n"
  "jmp qword ptr [rip+in_code]\n"
  ".globl leave_point\n"
  "leave_point:\n"
  "mov [rip+out_regs+0], rax\n"
  "mov [rip+out_regs+8], rcx\n"
  "mov [rip+out_regs+16], rbx\n"
  "mov [rip+out_regs+24], rdx\n"
  "mov [rip+out_regs+32], r8\n"
  "mov [rip+out_regs+40], r9\n"
  "mov [rip+out_regs+48], rsi\n"
  "mov [rip+out_regs+56], rdi\n"
  "mov [rip+out_regs+64], rbp\n"
  "mov [rip+out_regs+72], r10\n"
  "mov [rip+out_regs+80], r11\n"
  "mov [rip+out_regs+88], r12\n"
  "mov [rip+out_regs+96], r13\n"
  "mov [rip+out_regs+104], r14\n"
  "mov [rip+out_regs+112], r15\n"
  "mov [rip+out_regs+128], rsp\n"
  "pushfq\n"
  "pop qword ptr [rip+out_regs+120]\n"
  "mov rsp, [rip+host_rsp]\n"
  "pop r15\n"
  "pop r14\n"
  "pop r13\n"
  "pop r12\n"
  "pop rbp\n"
  "pop rbx\n"
  "ret\n"
  ".att_syntax prefix\n");

static void escape(int signal, siginfo_t *info, void *context)
{
  (void)info;
  (void)context;
  siglongjmp(rescue, signal);
}

static int fill(void *buffer, size_t size)
{
  size_t done = 0;
  while (done < size) {
    size_t count = fread((char *)buffer + done, 1, size - done, stdin);
    if (count == 0) return 0;
    done += count;
  }
  return 1;
}

static uint64_t word(const uint8_t *bytes)
{
  uint64_t value = 0;
  for (int i = 7; i >= 0; i--) value = value << 8 | bytes[i];
  return value;
}

int main(void)
{
  static uint8_t record[1 << 16];
  uint8_t *stack = mmap((void *)STACK_BASE, STACK_SIZE, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  uint8_t *code = mmap((void *)CODE_BASE, CODE_SIZE, PROT_READ | PROT_WRITE | PROT_EXEC,
    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  if (stack != (void *)STACK_BASE || code != (void *)CODE_BASE) return 2;
  uint8_t stub[14] = {0xff, 0x25, 0, 0, 0, 0};
  uint64_t target = (uint64_t)leave_point;
  memcpy(stub + 6, &target, 8);
  memcpy((void *)EXIT_STUB, stub, sizeof stub);
  static uint8_t alternate[1 << 16];
  stack_t altstack = {.ss_sp = alternate, .ss_size = sizeof alternate};
  sigaltstack(&altstack, NULL);
  struct sigaction action = {.sa_sigaction = escape, .sa_flags = SA_SIGINFO | SA_ONSTACK | SA_NODEFER};
  sigaction(SIGSEGV, &action, NULL);
  sigaction(SIGILL, &action, NULL);
  sigaction(SIGBUS, &action, NULL);
  sigaction(SIGFPE, &action, NULL);
  sigaction(SIGTRAP, &action, NULL);
  sigaction(SIGALRM, &action, NULL);
  uint32_t size;
  while (fill(&size, 4)) {
    if (size > sizeof record || !fill(record, size)) return 3;
    uint64_t n = record[57];
    uint64_t length = record[58 + 8 * n] | (uint64_t)record[59 + 8 * n] << 8;
    if (length > EXIT_STUB - CODE_BASE) return 4;
    memset(stack, 0xa5, STACK_SIZE);
    memcpy((void *)STACK_TOP, record + 58, 8 * n);
    memcpy(code, record + 60 + 8 * n, length);
    for (int i = 0; i < 6; i++) in_regs[i] = word(record + 8 * i);
    for (int i = 6; i < 15; i++) in_regs[i] = 0x0101010101010101ULL * (uint64_t)(i + 1);
    uint8_t flags = record[56];
    in_regs[15] = 0x202 | ((flags & 3) == 1 ? 0x40 : 0) | ((flags >> 2) == 1 ? 1 : 0);
    in_rsp = STACK_TOP;
    in_code = CODE_BASE;
    uint8_t status;
    int signal = sigsetjmp(rescue, 1);
    if (signal == 0) {
      alarm(1);
      enter();
      alarm(0);
      status = 1;
    } else {
      alarm(0);
      status = (uint8_t)(64 + signal);
      memset(out_regs, 0, sizeof out_regs);
    }
    fwrite(&status, 1, 1, stdout);
    fwrite(out_regs, 8, 17, stdout);
    uint64_t dump[DUMP] = {0};
    if (status == 1 && out_regs[16] >= STACK_BASE && out_regs[16] + 8 * DUMP <= STACK_BASE + STACK_SIZE)
      memcpy(dump, (void *)out_regs[16], sizeof dump);
    fwrite(dump, 8, DUMP, stdout);
  }
  return 0;
}
