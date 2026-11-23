//! The part of the output that is the same for every program: the system
//! layer (`@sys_write`, `@sys_exit`, the allocator `@rt_alloc`, `@rt_realloc`
//! and `@rt_free`), and on top of it the functions that build the text `show`
//! gives, write to the standard output and end a run with an error. The
//! system layer is the system's own, by system calls, or the C library's.

/// The characters from U+0080 that `show` of a `Text` writes as `\u{…}`,
/// as ranges `first last first last …` (the table of `totes/unicode`).
const ESCAPED: &str = include_str!("../../../totes/unicode/src/tables/escaped.txt");

/// `@.rt.escaped`: the ranges of `ESCAPED`, each its first and last
/// character as two 32-bit numbers, ended by a first character past every
/// character.
pub fn escaped() -> String {
    let mut bytes: Vec<u32> = ESCAPED
        .split(' ')
        .map(|n| n.trim().parse().expect("a number of the table"))
        .collect();
    bytes.extend([u32::MAX, u32::MAX]);
    let mut text = String::new();
    for n in &bytes {
        for b in n.to_le_bytes() {
            text.push_str(&format!("\\{b:02X}"));
        }
    }
    format!(
        "@.rt.escaped = private unnamed_addr constant [{} x i8] c\"{text}\"\n",
        4 * bytes.len()
    )
}

/// What the runtime stands on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sys {
    /// Linux on x86_64, by system calls: the program has its own `_start`,
    /// allocator and `memcpy`, and links no library (`-nostdlib -static`).
    Linux,
    /// A Linux with a C library: its start-up code and its entry points to
    /// the kernel (`write`, `exit`, `mmap`, `munmap`), and the runtime's own
    /// allocator on pages from `mmap`.
    Libc,
    /// For the tests that run the address sanitizer: as `Libc`, but every
    /// block is a block of `malloc`, which the sanitizer sees.
    Asan,
}

impl Sys {
    /// What the program of this machine is built on: system calls where
    /// there is a layer for them, the C library elsewhere. Never `Asan`.
    pub fn host() -> Sys {
        if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
            Sys::Linux
        } else {
            Sys::Libc
        }
    }

    /// The flags `clang` links the module's program with, besides the ones
    /// every module takes.
    pub fn link_flags(self) -> &'static [&'static str] {
        match self {
            Sys::Linux => &["-nostdlib", "-static"],
            Sys::Libc | Sys::Asan => &[],
        }
    }
}

/// The runtime: the declarations of the intrinsics it and the program use,
/// then the system layer, then the rest.
pub fn runtime(sys: Sys) -> String {
    match sys {
        Sys::Linux => format!("{INTRINSICS}{LINUX}{ALLOC}{SHARED}"),
        Sys::Libc => format!("{INTRINSICS}{LIBC}{ALLOC}{SHARED}"),
        Sys::Asan => format!("{INTRINSICS}{ASAN}{SHARED}"),
    }
}

const INTRINSICS: &str = r#"

declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
declare { i8, i1 } @llvm.sadd.with.overflow.i8(i8, i8)
declare { i8, i1 } @llvm.ssub.with.overflow.i8(i8, i8)
declare { i8, i1 } @llvm.smul.with.overflow.i8(i8, i8)
declare { i8, i1 } @llvm.uadd.with.overflow.i8(i8, i8)
declare { i8, i1 } @llvm.usub.with.overflow.i8(i8, i8)
declare { i8, i1 } @llvm.umul.with.overflow.i8(i8, i8)
declare { i16, i1 } @llvm.sadd.with.overflow.i16(i16, i16)
declare { i16, i1 } @llvm.ssub.with.overflow.i16(i16, i16)
declare { i16, i1 } @llvm.smul.with.overflow.i16(i16, i16)
declare { i16, i1 } @llvm.uadd.with.overflow.i16(i16, i16)
declare { i16, i1 } @llvm.usub.with.overflow.i16(i16, i16)
declare { i16, i1 } @llvm.umul.with.overflow.i16(i16, i16)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.ssub.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.uadd.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.usub.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.umul.with.overflow.i32(i32, i32)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.smul.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.usub.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64)

"#;

const LINUX: &str = r#"

; The system under the runtime, for Linux on x86_64: the program is its own
; entry point and asks the kernel for everything by system calls. It links
; no library. The calls the runtime makes of the system are `@sys_write`,
; `@sys_exit` and the allocator `@rt_alloc`, `@rt_realloc` and `@rt_free`;
; `memcpy`, `memmove`, `memset`, `memcmp` and `bcmp` are what LLVM itself
; calls.

; A system call by its number and six arguments. What it gives is a number
; from -4095 to -1 when the call fails.
define internal i64 @sys_call(i64 %nr, i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f) {
entry:
  %r = call i64 asm sideeffect "syscall", "={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9},~{rcx},~{r11},~{memory}"(i64 %nr, i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f)
  ret i64 %r
}

; `write`: how many bytes of the `n` at `p` went to the file `fd`, or a
; negative number.
define internal i64 @sys_write(i32 %fd, ptr %p, i64 %n) {
entry:
  %f = zext i32 %fd to i64
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 1, i64 %f, i64 %w, i64 %n, i64 0, i64 0, i64 0)
  ret i64 %r
}

; `exit_group`: the run ends with the code.
define internal void @sys_exit(i32 %code) noreturn {
entry:
  %c = zext i32 %code to i64
  %r = call i64 @sys_call(i64 231, i64 %c, i64 0, i64 0, i64 0, i64 0, i64 0)
  unreachable
}

; `getrandom`: the `n` bytes at `p` are random, from the kernel.
define internal void @sys_random(ptr %p, i64 %n) {
entry:
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 318, i64 %w, i64 %n, i64 0, i64 0, i64 0, i64 0)
  ret void
}

; `mmap`: `n` bytes of zeroed pages, a multiple of the page size, or null.
define internal ptr @sys_pages(i64 %n) {
entry:
  %r = call i64 @sys_call(i64 9, i64 0, i64 %n, i64 3, i64 34, i64 -1, i64 0)
  %bad = icmp ugt i64 %r, -4096
  br i1 %bad, label %fail, label %ok
ok:
  %p = inttoptr i64 %r to ptr
  ret ptr %p
fail:
  ret ptr null
}

; `munmap`: the pages are given back.
define internal void @sys_unpages(ptr %p, i64 %n) {
entry:
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 11, i64 %w, i64 %n, i64 0, i64 0, i64 0, i64 0)
  ret void
}

; `mremap`: the `old` bytes of pages at `p` become `n` bytes, perhaps
; elsewhere, or null.
define internal ptr @sys_remap(ptr %p, i64 %old, i64 %n) {
entry:
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 25, i64 %w, i64 %old, i64 %n, i64 1, i64 0, i64 0)
  %bad = icmp ugt i64 %r, -4096
  br i1 %bad, label %fail, label %ok
ok:
  %q = inttoptr i64 %r to ptr
  ret ptr %q
fail:
  ret ptr null
}

; What LLVM calls for a copy, a fill and a comparison of bytes. Each is a
; function of its own, so none may be turned back into a call of itself.
define ptr @memcpy(ptr %d, ptr %s, i64 %n) {
entry:
  %r = call { ptr, ptr, i64 } asm sideeffect "rep movsb", "={rdi},={rsi},={rcx},0,1,2,~{memory},~{dirflag},~{fpsr},~{flags}"(ptr %d, ptr %s, i64 %n)
  ret ptr %d
}

define ptr @memmove(ptr %d, ptr %s, i64 %n) {
entry:
  %back = icmp ugt ptr %d, %s
  br i1 %back, label %down, label %up
up:
  %r = call { ptr, ptr, i64 } asm sideeffect "rep movsb", "={rdi},={rsi},={rcx},0,1,2,~{memory},~{dirflag},~{fpsr},~{flags}"(ptr %d, ptr %s, i64 %n)
  ret ptr %d
down:
  %last = sub i64 %n, 1
  %de = getelementptr i8, ptr %d, i64 %last
  %se = getelementptr i8, ptr %s, i64 %last
  %r2 = call { ptr, ptr, i64 } asm sideeffect "std\0A rep movsb\0A cld", "={rdi},={rsi},={rcx},0,1,2,~{memory},~{dirflag},~{fpsr},~{flags}"(ptr %de, ptr %se, i64 %n)
  ret ptr %d
}

define ptr @memset(ptr %d, i32 %c, i64 %n) {
entry:
  %b = trunc i32 %c to i8
  %r = call { ptr, i64 } asm sideeffect "rep stosb", "={rdi},={rcx},0,1,{al},~{memory},~{dirflag},~{fpsr},~{flags}"(ptr %d, i64 %n, i8 %b)
  ret ptr %d
}

define i32 @memcmp(ptr %a, ptr %b, i64 %n) {
entry:
  %ip = alloca i64
  store i64 0, ptr %ip
  br label %head
head:
  %i = load i64, ptr %ip
  %more = icmp ult i64 %i, %n
  br i1 %more, label %body, label %same
body:
  %pa = getelementptr i8, ptr %a, i64 %i
  %pb = getelementptr i8, ptr %b, i64 %i
  %x = load i8, ptr %pa
  %y = load i8, ptr %pb
  %ne = icmp ne i8 %x, %y
  br i1 %ne, label %differ, label %next
differ:
  %xi = zext i8 %x to i32
  %yi = zext i8 %y to i32
  %d = sub i32 %xi, %yi
  ret i32 %d
next:
  %i1 = add i64 %i, 1
  store i64 %i1, ptr %ip
  br label %head
same:
  ret i32 0
}

define i32 @bcmp(ptr %a, ptr %b, i64 %n) {
entry:
  %r = call i32 @memcmp(ptr %a, ptr %b, i64 %n)
  ret i32 %r
}

define internal i64 @sys_open(ptr %p) {
entry:
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 2, i64 %w, i64 0, i64 0, i64 0, i64 0, i64 0)
  ret i64 %r
}

define internal i64 @sys_read(i64 %fd, ptr %p, i64 %n) {
entry:
  %w = ptrtoint ptr %p to i64
  %r = call i64 @sys_call(i64 0, i64 %fd, i64 %w, i64 %n, i64 0, i64 0, i64 0)
  ret i64 %r
}

define internal i64 @sys_close(i64 %fd) {
entry:
  %r = call i64 @sys_call(i64 3, i64 %fd, i64 0, i64 0, i64 0, i64 0, i64 0)
  ret i64 %r
}

; The program starts here with the stack aligned to 16 bytes, as the kernel
; leaves it, and ends with what `main` gives.
define void @rt_start(ptr %sp) noreturn {
entry:
  %argc = load i64, ptr %sp
  store i64 %argc, ptr @rt.argc
  %av = getelementptr i8, ptr %sp, i64 8
  store ptr %av, ptr @rt.argv
  %rc = call i32 @rt_main()
  call void @sys_exit(i32 %rc)
  unreachable
}

define void @_start() noreturn naked {
entry:
  call void asm sideeffect "xor %ebp, %ebp\0A mov %rsp, %rdi\0A call rt_start", "~{memory}"()
  unreachable
}
"#;

const LIBC: &str = r#"
; The system under the runtime, for a Linux with a C library (any machine
; but x86_64, where the layer of system calls is): the library's start-up
; code, which calls `main`, and its entry points to the kernel, `write`,
; `exit`, `mmap` and `munmap`. It takes no block from `malloc` and formats
; nothing: the allocator is the runtime's own. The constants of `mmap` are
; Linux's.

declare i64 @write(i32, ptr, i64)
declare void @exit(i32) noreturn
declare ptr @mmap(ptr, i64, i32, i32, i32, i64)
declare i32 @munmap(ptr, i64)
declare i32 @getentropy(ptr, i64)
declare i32 @memcmp(ptr, ptr, i64)

define internal i64 @sys_write(i32 %fd, ptr %p, i64 %n) {
entry:
  %r = call i64 @write(i32 %fd, ptr %p, i64 %n)
  ret i64 %r
}

define internal void @sys_random(ptr %p, i64 %n) {
entry:
  %r = call i32 @getentropy(ptr %p, i64 %n)
  ret void
}

define internal void @sys_exit(i32 %code) noreturn {
entry:
  call void @exit(i32 %code)
  unreachable
}

define internal ptr @sys_pages(i64 %n) {
entry:
  %p = call ptr @mmap(ptr null, i64 %n, i32 3, i32 34, i32 -1, i64 0)
  %w = ptrtoint ptr %p to i64
  %bad = icmp eq i64 %w, -1
  br i1 %bad, label %fail, label %ok
ok:
  ret ptr %p
fail:
  ret ptr null
}

define internal void @sys_unpages(ptr %p, i64 %n) {
entry:
  %r = call i32 @munmap(ptr %p, i64 %n)
  ret void
}

; The `old` bytes of pages at `p` become `n` bytes, which is more, elsewhere.
define internal ptr @sys_remap(ptr %p, i64 %old, i64 %n) {
entry:
  %q = call ptr @sys_pages(i64 %n)
  %none = icmp eq ptr %q, null
  br i1 %none, label %fail, label %ok
ok:
  call void @llvm.memcpy.p0.p0.i64(ptr %q, ptr %p, i64 %old, i1 false)
  call void @sys_unpages(ptr %p, i64 %old)
  ret ptr %q
fail:
  ret ptr null
}

declare i32 @open(ptr, i32, ...)
declare i64 @read(i32, ptr, i64)
declare i32 @close(i32)
declare ptr @__errno_location()

define internal i64 @sys_open(ptr %p) {
entry:
  %fd = call i32 (ptr, i32, ...) @open(ptr %p, i32 0)
  %fd64 = sext i32 %fd to i64
  %bad = icmp slt i64 %fd64, 0
  br i1 %bad, label %fail, label %ok
fail:
  %ep = call ptr @__errno_location()
  %e = load i32, ptr %ep
  %e64 = sext i32 %e to i64
  %neg = sub i64 0, %e64
  ret i64 %neg
ok:
  ret i64 %fd64
}

define internal i64 @sys_read(i64 %fd, ptr %p, i64 %n) {
entry:
  %f = trunc i64 %fd to i32
  %r = call i64 @read(i32 %f, ptr %p, i64 %n)
  %bad = icmp slt i64 %r, 0
  br i1 %bad, label %fail, label %ok
fail:
  %ep = call ptr @__errno_location()
  %e = load i32, ptr %ep
  %e64 = sext i32 %e to i64
  %neg = sub i64 0, %e64
  ret i64 %neg
ok:
  ret i64 %r
}

define internal i64 @sys_close(i64 %fd) {
entry:
  %f = trunc i64 %fd to i32
  %r = call i32 @close(i32 %f)
  ret i64 0
}

; The library's start-up code gives the arguments to `main`.
define i32 @main(i32 %argc, ptr %argv) {
entry:
  %c = sext i32 %argc to i64
  store i64 %c, ptr @rt.argc
  store ptr %argv, ptr @rt.argv
  %rc = call i32 @rt_main()
  ret i32 %rc
}
"#;

const ASAN: &str = r#"

; The system under the runtime for the tests that run the address sanitizer:
; the C library's `write`, `exit` and `memcmp`, and its `malloc`, `realloc`
; and `free` for every block, which the sanitizer sees. Nothing but those
; tests builds on it.

declare ptr @malloc(i64)
declare ptr @realloc(ptr, i64)
declare void @free(ptr)
declare i32 @getentropy(ptr, i64)
declare i32 @memcmp(ptr, ptr, i64)
declare i64 @write(i32, ptr, i64)
declare void @exit(i32) noreturn

@.rt.oom = private unnamed_addr constant [14 x i8] c"out of memory\00"

define internal i64 @sys_write(i32 %fd, ptr %p, i64 %n) {
entry:
  %r = call i64 @write(i32 %fd, ptr %p, i64 %n)
  ret i64 %r
}

define internal void @sys_random(ptr %p, i64 %n) {
entry:
  %r = call i32 @getentropy(ptr %p, i64 %n)
  ret void
}

define internal void @sys_exit(i32 %code) noreturn {
entry:
  call void @exit(i32 %code)
  unreachable
}

declare i32 @open(ptr, i32, ...)
declare i64 @read(i32, ptr, i64)
declare i32 @close(i32)
declare ptr @__errno_location()

define internal i64 @sys_open(ptr %p) {
entry:
  %fd = call i32 (ptr, i32, ...) @open(ptr %p, i32 0)
  %fd64 = sext i32 %fd to i64
  %bad = icmp slt i64 %fd64, 0
  br i1 %bad, label %fail, label %ok
fail:
  %ep = call ptr @__errno_location()
  %e = load i32, ptr %ep
  %e64 = sext i32 %e to i64
  %neg = sub i64 0, %e64
  ret i64 %neg
ok:
  ret i64 %fd64
}

define internal i64 @sys_read(i64 %fd, ptr %p, i64 %n) {
entry:
  %f = trunc i64 %fd to i32
  %r = call i64 @read(i32 %f, ptr %p, i64 %n)
  %bad = icmp slt i64 %r, 0
  br i1 %bad, label %fail, label %ok
fail:
  %ep = call ptr @__errno_location()
  %e = load i32, ptr %ep
  %e64 = sext i32 %e to i64
  %neg = sub i64 0, %e64
  ret i64 %neg
ok:
  ret i64 %r
}

define internal i64 @sys_close(i64 %fd) {
entry:
  %f = trunc i64 %fd to i32
  %r = call i32 @close(i32 %f)
  ret i64 0
}

; The library's start-up code gives the arguments to `main`.
define i32 @main(i32 %argc, ptr %argv) {
entry:
  %c = sext i32 %argc to i64
  store i64 %c, ptr @rt.argc
  store ptr %argv, ptr @rt.argv
  %rc = call i32 @rt_main()
  ret i32 %rc
}

define internal ptr @rt_alloc(i64 %n) {
entry:
  %p = call ptr @malloc(i64 %n)
  %none = icmp eq ptr %p, null
  br i1 %none, label %oom, label %ok
ok:
  ret ptr %p
oom:
  call void @rt_fail(ptr @.rt.oom)
  unreachable
}

define internal ptr @rt_realloc(ptr %p, i64 %n) {
entry:
  %q = call ptr @realloc(ptr %p, i64 %n)
  %none = icmp eq ptr %q, null
  br i1 %none, label %oom, label %ok
ok:
  ret ptr %q
oom:
  call void @rt_fail(ptr @.rt.oom)
  unreachable
}

define internal void @rt_free(ptr %p) {
entry:
  call void @free(ptr %p)
  ret void
}
"#;

const ALLOC: &str = r#"
@.rt.oom = private unnamed_addr constant [14 x i8] c"out of memory\00"

; The allocator. A block is a header of 16 bytes and the bytes the program
; asked for. The header's first word is the size class of a small block: its
; size is `1 << class`, from 32 bytes to 64 KiB. A freed small block goes on
; the list of its class and is the next one given for it; it is never given
; back. Small blocks are cut from chunks of 1 MiB. A block bigger than that
; has pages of its own: its header's first word is 0 and the second the bytes
; of its pages. A block is aligned to 16 bytes.
@rt.bump = internal global ptr null
@rt.bump_end = internal global ptr null
@rt.free = internal global [32 x ptr] zeroinitializer

define internal ptr @rt_alloc(i64 %n) {
entry:
  %kp = alloca i64
  %sp = alloca i64
  %huge = icmp ugt i64 %n, 4611686018427387904
  br i1 %huge, label %oom, label %sized
sized:
  %need = add i64 %n, 16
  %small = icmp ule i64 %need, 65536
  br i1 %small, label %cls, label %large
cls:
  store i64 5, ptr %kp
  store i64 32, ptr %sp
  br label %clshead
clshead:
  %size = load i64, ptr %sp
  %fits = icmp uge i64 %size, %need
  br i1 %fits, label %have, label %clsnext
clsnext:
  %size2 = shl i64 %size, 1
  store i64 %size2, ptr %sp
  %k0 = load i64, ptr %kp
  %k1 = add i64 %k0, 1
  store i64 %k1, ptr %kp
  br label %clshead
have:
  %k = load i64, ptr %kp
  %slot = getelementptr ptr, ptr @rt.free, i64 %k
  %head = load ptr, ptr %slot
  %any = icmp ne ptr %head, null
  br i1 %any, label %reuse, label %carve
reuse:
  %nextp = load ptr, ptr %head
  store ptr %nextp, ptr %slot
  ret ptr %head
carve:
  %bump = load ptr, ptr @rt.bump
  %end = load ptr, ptr @rt.bump_end
  %bi = ptrtoint ptr %bump to i64
  %ei = ptrtoint ptr %end to i64
  %room = sub i64 %ei, %bi
  %ok = icmp ule i64 %size, %room
  br i1 %ok, label %cut, label %chunk
chunk:
  %c = call ptr @sys_pages(i64 1048576)
  %none = icmp eq ptr %c, null
  br i1 %none, label %oom, label %fresh
fresh:
  %cend = getelementptr i8, ptr %c, i64 1048576
  store ptr %c, ptr @rt.bump
  store ptr %cend, ptr @rt.bump_end
  br label %cut
cut:
  %b = load ptr, ptr @rt.bump
  %b2 = getelementptr i8, ptr %b, i64 %size
  store ptr %b2, ptr @rt.bump
  store i64 %k, ptr %b
  %pl = getelementptr i8, ptr %b, i64 16
  ret ptr %pl
large:
  %t = add i64 %need, 4095
  %total = and i64 %t, -4096
  %m = call ptr @sys_pages(i64 %total)
  %mnone = icmp eq ptr %m, null
  br i1 %mnone, label %oom, label %lok
lok:
  store i64 0, ptr %m
  %mt = getelementptr i8, ptr %m, i64 8
  store i64 %total, ptr %mt
  %lp = getelementptr i8, ptr %m, i64 16
  ret ptr %lp
oom:
  call void @rt_fail(ptr @.rt.oom)
  unreachable
}

; The block of `p` is free. A null address is no block.
define internal void @rt_free(ptr %p) {
entry:
  %null = icmp eq ptr %p, null
  br i1 %null, label %done, label %live
live:
  %h = getelementptr i8, ptr %p, i64 -16
  %k = load i64, ptr %h
  %large = icmp eq i64 %k, 0
  br i1 %large, label %big, label %small
big:
  %tp = getelementptr i8, ptr %h, i64 8
  %total = load i64, ptr %tp
  call void @sys_unpages(ptr %h, i64 %total)
  ret void
small:
  %slot = getelementptr ptr, ptr @rt.free, i64 %k
  %head = load ptr, ptr %slot
  store ptr %head, ptr %p
  store ptr %p, ptr %slot
  ret void
done:
  ret void
}

; The block of `p` has room for `n` bytes: the same block when it has it,
; or another with the bytes of the first.
define internal ptr @rt_realloc(ptr %p, i64 %n) {
entry:
  %null = icmp eq ptr %p, null
  br i1 %null, label %fresh, label %have
fresh:
  %f = call ptr @rt_alloc(i64 %n)
  ret ptr %f
have:
  %h = getelementptr i8, ptr %p, i64 -16
  %k = load i64, ptr %h
  %large = icmp eq i64 %k, 0
  br i1 %large, label %big, label %small
small:
  %size = shl i64 1, %k
  %cap = sub i64 %size, 16
  %fits = icmp ule i64 %n, %cap
  br i1 %fits, label %same, label %move
move:
  %q = call ptr @rt_alloc(i64 %n)
  call void @llvm.memcpy.p0.p0.i64(ptr %q, ptr %p, i64 %cap, i1 false)
  call void @rt_free(ptr %p)
  ret ptr %q
big:
  %tp = getelementptr i8, ptr %h, i64 8
  %total = load i64, ptr %tp
  %bcap = sub i64 %total, 16
  %bfits = icmp ule i64 %n, %bcap
  br i1 %bfits, label %same, label %grow
grow:
  %huge = icmp ugt i64 %n, 4611686018427387904
  br i1 %huge, label %oom, label %remap
remap:
  %need = add i64 %n, 16
  %t = add i64 %need, 4095
  %ntotal = and i64 %t, -4096
  %m = call ptr @sys_remap(ptr %h, i64 %total, i64 %ntotal)
  %mnone = icmp eq ptr %m, null
  br i1 %mnone, label %oom, label %mok
mok:
  %mt = getelementptr i8, ptr %m, i64 8
  store i64 %ntotal, ptr %mt
  %lp = getelementptr i8, ptr %m, i64 16
  ret ptr %lp
same:
  ret ptr %p
oom:
  call void @rt_fail(ptr @.rt.oom)
  unreachable
}

"#;

const SHARED: &str = r#"

; The chain of handlers: each entry is the next entry, the number of an
; operation and the function value of its arm.
@rt.ev = internal global ptr null
@rt.argc = internal global i64 0
@rt.argv = internal global ptr null

; The nearest entry of the chain for the operation, or null.
define internal ptr @rt_find(i64 %op) {
entry:
  %first = load ptr, ptr @rt.ev
  %ep = alloca i64
  %w = ptrtoint ptr %first to i64
  store i64 %w, ptr %ep
  br label %head
head:
  %ew = load i64, ptr %ep
  %e = inttoptr i64 %ew to ptr
  %none = icmp eq ptr %e, null
  br i1 %none, label %miss, label %test
test:
  %opp = getelementptr i64, ptr %e, i64 1
  %o = load i64, ptr %opp
  %hit = icmp eq i64 %o, %op
  br i1 %hit, label %found, label %next
next:
  %nw = load i64, ptr %e
  store i64 %nw, ptr %ep
  br label %head
found:
  ret ptr %e
miss:
  ret ptr null
}

; A text being built: its bytes, how many there are, how many there is room for.
%Buf = type { ptr, i64, i64 }

@.rt.empty = private unnamed_addr constant [1 x i8] c"\00"
@.rt.quote = private unnamed_addr constant [2 x i8] c"\22\00"
@.rt.esc.quote = private unnamed_addr constant [3 x i8] c"\5C\22\00"
@.rt.esc.back = private unnamed_addr constant [3 x i8] c"\5C\5C\00"
@.rt.esc.nl = private unnamed_addr constant [3 x i8] c"\5Cn\00"
@.rt.esc.cr = private unnamed_addr constant [3 x i8] c"\5Cr\00"
@.rt.esc.tab = private unnamed_addr constant [3 x i8] c"\5Ct\00"
@.rt.esc.nul = private unnamed_addr constant [3 x i8] c"\5C0\00"
@.rt.esc.hexo = private unnamed_addr constant [4 x i8] c"\5Cu{\00"
@.rt.esc.hexc = private unnamed_addr constant [2 x i8] c"}\00"
@.rt.eq = private unnamed_addr constant [4 x i8] c" = \00"
@.rt.nl = private unnamed_addr constant [2 x i8] c"\0A\00"
@.rt.error = private unnamed_addr constant [8 x i8] c"error: \00"

define internal void @rt_push(ptr %b, ptr %s, i64 %n) {
entry:
  %lenp = getelementptr %Buf, ptr %b, i32 0, i32 1
  %capp = getelementptr %Buf, ptr %b, i32 0, i32 2
  %len = load i64, ptr %lenp
  %cap = load i64, ptr %capp
  %need = add i64 %len, %n
  %need1 = add i64 %need, 1
  %fits = icmp ule i64 %need1, %cap
  br i1 %fits, label %copy, label %grow
grow:
  %twice = shl i64 %need1, 1
  %data0 = load ptr, ptr %b
  %data1 = call ptr @rt_realloc(ptr %data0, i64 %twice)
  store ptr %data1, ptr %b
  store i64 %twice, ptr %capp
  br label %copy
copy:
  %data = load ptr, ptr %b
  %at = getelementptr i8, ptr %data, i64 %len
  call void @llvm.memcpy.p0.p0.i64(ptr %at, ptr %s, i64 %n, i1 false)
  store i64 %need, ptr %lenp
  ret void
}

define internal void @rt_push_str(ptr %b, ptr %s) {
entry:
  %n = call i64 @rt_strlen(ptr %s)
  call void @rt_push(ptr %b, ptr %s, i64 %n)
  ret void
}

define internal void @rt_push_i64(ptr %b, i64 %v) {
entry:
  %tmp = alloca [32 x i8]
  %off = call i64 @rt_fmt_i64(ptr %tmp, i64 %v)
  %at = getelementptr i8, ptr %tmp, i64 %off
  %n = sub i64 32, %off
  call void @rt_push(ptr %b, ptr %at, i64 %n)
  ret void
}

define internal void @rt_push_u64(ptr %b, i64 %v) {
entry:
  %tmp = alloca [32 x i8]
  %off = call i64 @rt_fmt_u64(ptr %tmp, i64 %v)
  %at = getelementptr i8, ptr %tmp, i64 %off
  %n = sub i64 32, %off
  call void @rt_push(ptr %b, ptr %at, i64 %n)
  ret void
}

; `\u{` and the number in lowercase hexadecimal and `}`.
define internal void @rt_push_hex(ptr %b, i64 %v) {
entry:
  %tmp = alloca [16 x i8]
  %end = getelementptr i8, ptr %tmp, i64 16
  %start = call ptr @rt_digits(ptr %end, i64 %v, i64 16)
  %e = ptrtoint ptr %end to i64
  %s = ptrtoint ptr %start to i64
  %n = sub i64 %e, %s
  call void @rt_push(ptr %b, ptr @.rt.esc.hexo, i64 3)
  call void @rt_push(ptr %b, ptr %start, i64 %n)
  call void @rt_push(ptr %b, ptr @.rt.esc.hexc, i64 1)
  ret void
}

; The text built, ended with a zero byte; the caller frees it.
define internal ptr @rt_finish(ptr %b) {
entry:
  call void @rt_push(ptr %b, ptr @.rt.empty, i64 0)
  %lenp = getelementptr %Buf, ptr %b, i32 0, i32 1
  %len = load i64, ptr %lenp
  %data = load ptr, ptr %b
  %end = getelementptr i8, ptr %data, i64 %len
  store i8 0, ptr %end
  ret ptr %data
}

; A box for a `Text` of `n` bytes, `{ count, n, bytes, 0 }`, with its
; bytes not written but the last zero.
define internal ptr @rt_text_new(i64 %n) {
entry:
  %size = add i64 %n, 17
  %t = call ptr @rt_alloc(i64 %size)
  store i64 1, ptr %t
  %lenp = getelementptr i64, ptr %t, i64 1
  store i64 %n, ptr %lenp
  %data = getelementptr i8, ptr %t, i64 16
  %end = getelementptr i8, ptr %data, i64 %n
  store i8 0, ptr %end
  ret ptr %t
}

; A `Text` of the `n` bytes at `s`.
define internal ptr @rt_text(ptr %s, i64 %n) {
entry:
  %t = call ptr @rt_text_new(i64 %n)
  %data = getelementptr i8, ptr %t, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr %data, ptr %s, i64 %n, i1 false)
  ret ptr %t
}

; One value fewer shares the text; the last frees it. A literal's box
; (count 0) is constant and stays.
define internal void @rt_text_drop(ptr %t) {
entry:
  %rc = load i64, ptr %t
  %lit = icmp eq i64 %rc, 0
  br i1 %lit, label %stay, label %counted
stay:
  ret void
counted:
  %last = icmp eq i64 %rc, 1
  br i1 %last, label %free, label %keep
free:
  call void @rt_free(ptr %t)
  ret void
keep:
  %less = sub i64 %rc, 1
  store i64 %less, ptr %t
  ret void
}

; One value more shares the text. A literal's box (count 0) is constant.
define internal void @rt_text_dup(ptr %t) {
entry:
  %rc = load i64, ptr %t
  %lit = icmp eq i64 %rc, 0
  br i1 %lit, label %stay, label %counted
stay:
  ret void
counted:
  %more = add i64 %rc, 1
  store i64 %more, ptr %t
  ret void
}

define internal i64 @rt_text_len(ptr %t) {
entry:
  %lenp = getelementptr i64, ptr %t, i64 1
  %n = load i64, ptr %lenp
  ret i64 %n
}

; Whether the text holds the `n` bytes at `s`.
define internal i1 @rt_text_is(ptr %t, ptr %s, i64 %n) {
entry:
  %len = call i64 @rt_text_len(ptr %t)
  %same = icmp eq i64 %len, %n
  br i1 %same, label %bytes, label %no
bytes:
  %data = getelementptr i8, ptr %t, i64 16
  %c = call i32 @memcmp(ptr %data, ptr %s, i64 %n)
  %eq = icmp eq i32 %c, 0
  ret i1 %eq
no:
  ret i1 false
}

define internal i1 @rt_text_eq(ptr %a, ptr %b) {
entry:
  %data = getelementptr i8, ptr %b, i64 16
  %n = call i64 @rt_text_len(ptr %b)
  %eq = call i1 @rt_text_is(ptr %a, ptr %data, i64 %n)
  ret i1 %eq
}

; The text of `a`'s bytes then `b`'s.
define internal ptr @rt_text_concat(ptr %a, ptr %b) {
entry:
  %na = call i64 @rt_text_len(ptr %a)
  %nb = call i64 @rt_text_len(ptr %b)
  %n = add i64 %na, %nb
  %t = call ptr @rt_text_new(i64 %n)
  %da = getelementptr i8, ptr %a, i64 16
  %db = getelementptr i8, ptr %b, i64 16
  %data = getelementptr i8, ptr %t, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr %data, ptr %da, i64 %na, i1 false)
  %at = getelementptr i8, ptr %data, i64 %na
  call void @llvm.memcpy.p0.p0.i64(ptr %at, ptr %db, i64 %nb, i1 false)
  ret ptr %t
}

; The text a number is written as: signed, or not.
define internal ptr @rt_text_of_i64(i64 %v) {
entry:
  %tmp = alloca [32 x i8]
  %off = call i64 @rt_fmt_i64(ptr %tmp, i64 %v)
  %at = getelementptr i8, ptr %tmp, i64 %off
  %n = sub i64 32, %off
  %t = call ptr @rt_text(ptr %at, i64 %n)
  ret ptr %t
}

define internal ptr @rt_text_of_u64(i64 %v) {
entry:
  %tmp = alloca [32 x i8]
  %off = call i64 @rt_fmt_u64(ptr %tmp, i64 %v)
  %at = getelementptr i8, ptr %tmp, i64 %off
  %n = sub i64 32, %off
  %t = call ptr @rt_text(ptr %at, i64 %n)
  ret ptr %t
}

; The byte of a `Text` at `i`, as an `Option(u8)`: `None`, or `Some` and the
; byte.
define internal [2 x i64] @rt_text_byte(ptr %t, i64 %i) {
entry:
  %n = call i64 @rt_text_len(ptr %t)
  %in = icmp ult i64 %i, %n
  br i1 %in, label %some, label %none
some:
  %d = getelementptr i8, ptr %t, i64 16
  %p = getelementptr i8, ptr %d, i64 %i
  %c = load i8, ptr %p
  %w = zext i8 %c to i64
  %a = insertvalue [2 x i64] zeroinitializer, i64 1, 0
  %b = insertvalue [2 x i64] %a, i64 %w, 1
  ret [2 x i64] %b
none:
  ret [2 x i64] zeroinitializer
}

; Whether position `i` of the bytes `d` of `n` bytes begins a character, or is
; the end.
define internal i1 @rt_text_boundary(ptr %d, i64 %i, i64 %n) {
entry:
  %end = icmp uge i64 %i, %n
  br i1 %end, label %yes, label %check
check:
  %p = getelementptr i8, ptr %d, i64 %i
  %c = load i8, ptr %p
  %z = zext i8 %c to i64
  %m = and i64 %z, 192
  %cont = icmp eq i64 %m, 128
  br i1 %cont, label %no, label %yes
yes:
  ret i1 true
no:
  ret i1 false
}

; The bytes `s` to `en` of a `Text` as an `Option(Text)`: `None` when they are
; not in the text in that order or an end is inside a character.
define internal [2 x i64] @rt_text_slice(ptr %t, i64 %s, i64 %en) {
entry:
  %n = call i64 @rt_text_len(ptr %t)
  %a = icmp ule i64 %s, %en
  br i1 %a, label %c1, label %none
c1:
  %b = icmp ule i64 %en, %n
  br i1 %b, label %c2, label %none
c2:
  %d = getelementptr i8, ptr %t, i64 16
  %ok1 = call i1 @rt_text_boundary(ptr %d, i64 %s, i64 %n)
  br i1 %ok1, label %c3, label %none
c3:
  %ok2 = call i1 @rt_text_boundary(ptr %d, i64 %en, i64 %n)
  br i1 %ok2, label %some, label %none
some:
  %p = getelementptr i8, ptr %d, i64 %s
  %len = sub i64 %en, %s
  %r = call ptr @rt_text(ptr %p, i64 %len)
  %w = ptrtoint ptr %r to i64
  %x = insertvalue [2 x i64] zeroinitializer, i64 1, 0
  %y = insertvalue [2 x i64] %x, i64 %w, 1
  ret [2 x i64] %y
none:
  ret [2 x i64] zeroinitializer
}

; -1, 0 or 1 as the bytes of `a` are before, equal to or after those of `b`.
define internal i64 @rt_text_compare(ptr %a, ptr %b) {
entry:
  %la = call i64 @rt_text_len(ptr %a)
  %lb = call i64 @rt_text_len(ptr %b)
  %mp = alloca i64
  store i64 %lb, ptr %mp
  %lt = icmp ult i64 %la, %lb
  br i1 %lt, label %setmin, label %cmp
setmin:
  store i64 %la, ptr %mp
  br label %cmp
cmp:
  %m = load i64, ptr %mp
  %da = getelementptr i8, ptr %a, i64 16
  %db = getelementptr i8, ptr %b, i64 16
  %r = call i32 @memcmp(ptr %da, ptr %db, i64 %m)
  %neg = icmp slt i32 %r, 0
  br i1 %neg, label %less, label %c2
c2:
  %pos = icmp sgt i32 %r, 0
  br i1 %pos, label %more, label %c3
c3:
  %sl = icmp ult i64 %la, %lb
  br i1 %sl, label %less, label %c4
c4:
  %sg = icmp ugt i64 %la, %lb
  br i1 %sg, label %more, label %same
less:
  ret i64 -1
more:
  ret i64 1
same:
  ret i64 0
}

; Adds a `Text` as `show` writes one: in quotes, with `"`, `\`, a line
; break, a carriage return, a tab and a zero byte escaped by a backslash, and
; every other control character and each character of `@.rt.escaped` as
; `\u{…}` in hexadecimal. Every other character is written as it is.
define internal void @rt_push_text(ptr %b, ptr %t) {
entry:
  call void @rt_push(ptr %b, ptr @.rt.quote, i64 1)
  call void @rt_push_escaped(ptr %b, ptr %t)
  call void @rt_push(ptr %b, ptr @.rt.quote, i64 1)
  ret void
}

; The bytes of a `Text` as `show` writes them, without the quotes.
define internal void @rt_push_escaped(ptr %b, ptr %t) {
entry:
  %ip = alloca i64
  %np = alloca i64
  %cpp = alloca i64
  %kp = alloca i64
  store i64 0, ptr %ip
  %n = call i64 @rt_text_len(ptr %t)
  %data = getelementptr i8, ptr %t, i64 16
  br label %head
head:
  %i = load i64, ptr %ip
  %more = icmp ult i64 %i, %n
  br i1 %more, label %byte, label %done
byte:
  %at = getelementptr i8, ptr %data, i64 %i
  %c = load i8, ptr %at
  store i64 1, ptr %np
  %wide = icmp slt i8 %c, 0
  br i1 %wide, label %lead, label %ascii
ascii:
  switch i8 %c, label %other [ i8 34, label %quote i8 92, label %back i8 10, label %nl i8 13, label %cr i8 9, label %tab i8 0, label %nul i8 127, label %ctl ]
quote:
  call void @rt_push(ptr %b, ptr @.rt.esc.quote, i64 2)
  br label %next
back:
  call void @rt_push(ptr %b, ptr @.rt.esc.back, i64 2)
  br label %next
nl:
  call void @rt_push(ptr %b, ptr @.rt.esc.nl, i64 2)
  br label %next
cr:
  call void @rt_push(ptr %b, ptr @.rt.esc.cr, i64 2)
  br label %next
tab:
  call void @rt_push(ptr %b, ptr @.rt.esc.tab, i64 2)
  br label %next
nul:
  call void @rt_push(ptr %b, ptr @.rt.esc.nul, i64 2)
  br label %next
other:
  %low = icmp ult i8 %c, 32
  br i1 %low, label %ctl, label %raw
ctl:
  %cz = zext i8 %c to i64
  store i64 %cz, ptr %cpp
  br label %hex
lead:
  %c0 = zext i8 %c to i64
  %at1 = getelementptr i8, ptr %at, i64 1
  %d1 = load i8, ptr %at1
  %e1 = zext i8 %d1 to i64
  %x1 = and i64 %e1, 63
  %four = icmp uge i64 %c0, 240
  br i1 %four, label %lead4, label %lead3or2
lead3or2:
  %three = icmp uge i64 %c0, 224
  br i1 %three, label %lead3, label %lead2
lead2:
  %h2 = and i64 %c0, 31
  %s2 = shl i64 %h2, 6
  %cp2 = add i64 %s2, %x1
  store i64 2, ptr %np
  store i64 %cp2, ptr %cpp
  br label %search
lead3:
  %at2 = getelementptr i8, ptr %at, i64 2
  %d2 = load i8, ptr %at2
  %e2 = zext i8 %d2 to i64
  %x2 = and i64 %e2, 63
  %h3 = and i64 %c0, 15
  %s3 = shl i64 %h3, 12
  %t3 = shl i64 %x1, 6
  %u3 = add i64 %s3, %t3
  %cp3 = add i64 %u3, %x2
  store i64 3, ptr %np
  store i64 %cp3, ptr %cpp
  br label %search
lead4:
  %at2f = getelementptr i8, ptr %at, i64 2
  %d2f = load i8, ptr %at2f
  %e2f = zext i8 %d2f to i64
  %x2f = and i64 %e2f, 63
  %at3 = getelementptr i8, ptr %at, i64 3
  %d3 = load i8, ptr %at3
  %e3 = zext i8 %d3 to i64
  %x3 = and i64 %e3, 63
  %h4 = and i64 %c0, 7
  %s4 = shl i64 %h4, 18
  %t4 = shl i64 %x1, 12
  %u4 = shl i64 %x2f, 6
  %v4 = add i64 %s4, %t4
  %w4 = add i64 %v4, %u4
  %cp4 = add i64 %w4, %x3
  store i64 4, ptr %np
  store i64 %cp4, ptr %cpp
  br label %search
search:
  store i64 0, ptr %kp
  br label %probe
probe:
  %k = load i64, ptr %kp
  %cp = load i64, ptr %cpp
  %k2 = shl i64 %k, 1
  %firstp = getelementptr i32, ptr @.rt.escaped, i64 %k2
  %first32 = load i32, ptr %firstp
  %first = zext i32 %first32 to i64
  %past = icmp ugt i64 %first, %cp
  br i1 %past, label %raw, label %inside
inside:
  %k21 = add i64 %k2, 1
  %lastp = getelementptr i32, ptr @.rt.escaped, i64 %k21
  %last32 = load i32, ptr %lastp
  %last = zext i32 %last32 to i64
  %within = icmp ule i64 %cp, %last
  br i1 %within, label %hex, label %step
step:
  %k1 = add i64 %k, 1
  store i64 %k1, ptr %kp
  br label %probe
hex:
  %v = load i64, ptr %cpp
  call void @rt_push_hex(ptr %b, i64 %v)
  br label %next
raw:
  %len = load i64, ptr %np
  call void @rt_push(ptr %b, ptr %at, i64 %len)
  br label %next
next:
  %step1 = load i64, ptr %np
  %i1 = add i64 %i, %step1
  store i64 %i1, ptr %ip
  br label %head
done:
  ret void
}

; A new `Text` of what `show` writes of the bytes of `t`, without the quotes.
define internal ptr @rt_text_escape_debug(ptr %t) {
entry:
  %b = alloca %Buf
  store %Buf zeroinitializer, ptr %b
  call void @rt_push_escaped(ptr %b, ptr %t)
  %s = call ptr @rt_finish(ptr %b)
  %lenp = getelementptr %Buf, ptr %b, i32 0, i32 1
  %n = load i64, ptr %lenp
  %r = call ptr @rt_text(ptr %s, i64 %n)
  call void @rt_free(ptr %s)
  ret ptr %r
}

; A `Vec`: the address of its header of three words, the address of the
; elements, how many there are and how many there is room for. The elements
; are rows of `n` words one after another, `n` being the words of one.
define internal ptr @rt_vec_new() {
entry:
  %h = call ptr @rt_alloc(i64 24)
  store ptr null, ptr %h
  %lenp = getelementptr i64, ptr %h, i64 1
  store i64 0, ptr %lenp
  %capp = getelementptr i64, ptr %h, i64 2
  store i64 0, ptr %capp
  ret ptr %h
}

; The `n` words at `x` are added as the last element.
define internal void @rt_vec_push(ptr %v, ptr %x, i64 %n) {
entry:
  %lenp = getelementptr i64, ptr %v, i64 1
  %capp = getelementptr i64, ptr %v, i64 2
  %len = load i64, ptr %lenp
  %cap = load i64, ptr %capp
  %full = icmp eq i64 %len, %cap
  br i1 %full, label %grow, label %copy
grow:
  %twice = shl i64 %cap, 1
  %cap1 = add i64 %twice, 4
  %rows = mul i64 %cap1, %n
  %words = add i64 %rows, 1
  %bytes = shl i64 %words, 3
  %data0 = load ptr, ptr %v
  %data1 = call ptr @rt_realloc(ptr %data0, i64 %bytes)
  store ptr %data1, ptr %v
  store i64 %cap1, ptr %capp
  br label %copy
copy:
  %data = load ptr, ptr %v
  %off = mul i64 %len, %n
  %at = getelementptr i64, ptr %data, i64 %off
  %size = shl i64 %n, 3
  call void @llvm.memcpy.p0.p0.i64(ptr %at, ptr %x, i64 %size, i1 false)
  %len1 = add i64 %len, 1
  store i64 %len1, ptr %lenp
  ret void
}

; The address of element `i`, or null when there is none.
define internal ptr @rt_vec_at(ptr %v, i64 %i, i64 %n) {
entry:
  %lenp = getelementptr i64, ptr %v, i64 1
  %len = load i64, ptr %lenp
  %in = icmp ult i64 %i, %len
  br i1 %in, label %hit, label %miss
hit:
  %data = load ptr, ptr %v
  %off = mul i64 %i, %n
  %p = getelementptr i64, ptr %data, i64 %off
  ret ptr %p
miss:
  ret ptr null
}

; The address of the last element, or null when there is none.
define internal ptr @rt_vec_last(ptr %v, i64 %n) {
entry:
  %lenp = getelementptr i64, ptr %v, i64 1
  %len = load i64, ptr %lenp
  %none = icmp eq i64 %len, 0
  br i1 %none, label %miss, label %hit
hit:
  %i = sub i64 %len, 1
  %p = call ptr @rt_vec_at(ptr %v, i64 %i, i64 %n)
  ret ptr %p
miss:
  ret ptr null
}

; Takes the last element out: its address, which holds it until the next
; push, or null when there is none.
define internal ptr @rt_vec_pop(ptr %v, i64 %n) {
entry:
  %lenp = getelementptr i64, ptr %v, i64 1
  %len = load i64, ptr %lenp
  %none = icmp eq i64 %len, 0
  br i1 %none, label %miss, label %hit
hit:
  %i = sub i64 %len, 1
  store i64 %i, ptr %lenp
  %data = load ptr, ptr %v
  %off = mul i64 %i, %n
  %p = getelementptr i64, ptr %data, i64 %off
  ret ptr %p
miss:
  ret ptr null
}

; Swaps elements `i` and `j` when both are there, and says whether it did.
define internal i1 @rt_vec_swap(ptr %v, i64 %i, i64 %j, i64 %n) {
entry:
  %kp = alloca i64
  %a = call ptr @rt_vec_at(ptr %v, i64 %i, i64 %n)
  %b = call ptr @rt_vec_at(ptr %v, i64 %j, i64 %n)
  %noa = icmp eq ptr %a, null
  br i1 %noa, label %no, label %other
other:
  %nob = icmp eq ptr %b, null
  br i1 %nob, label %no, label %start
start:
  store i64 0, ptr %kp
  br label %head
head:
  %k = load i64, ptr %kp
  %more = icmp ult i64 %k, %n
  br i1 %more, label %body, label %done
body:
  %pa = getelementptr i64, ptr %a, i64 %k
  %pb = getelementptr i64, ptr %b, i64 %k
  %x = load i64, ptr %pa
  %y = load i64, ptr %pb
  store i64 %y, ptr %pa
  store i64 %x, ptr %pb
  %k1 = add i64 %k, 1
  store i64 %k1, ptr %kp
  br label %head
done:
  ret i1 true
no:
  ret i1 false
}

; The elements' room and the header are released: each element has been
; dropped already.
define internal void @rt_vec_free(ptr %v) {
entry:
  %data = load ptr, ptr %v
  call void @rt_free(ptr %data)
  call void @rt_free(ptr %v)
  ret void
}

; `Slots`: the address of a header of `5 + sn` words — the address of the
; elements (rows of `n` words, one per slot), the capacity, the address of the
; flags (a word per slot, 1 when the slot holds an element), the address of the
; marks (rows of `mn` words, one per slot), the address of the vacant mark
; (`mn` words: what `mark` returns past the capacity), then the `sn` words of
; the state. The runtime keeps the flags itself: only the flagged slots hold
; an element, which the drop of the type frees. Allocation sizes are checked
; for overflow before the heap is asked; a slot past the capacity is refused
; by the builtins that read or write an element.

@.rt.slots_overflow = private unnamed_addr constant [28 x i8] c"Slots: allocation too large\00"
@.rt.slots_oob = private unnamed_addr constant [26 x i8] c"Slots: index out of range\00"
@.rt.slots_empty = private unnamed_addr constant [27 x i8] c"Slots: slot holds no value\00"

; Bytes for `count` rows of `n` words plus one length word, or fail on overflow.
define internal i64 @rt_slots_row_bytes(i64 %count, i64 %n) {
entry:
  %m = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %count, i64 %n)
  %rows = extractvalue { i64, i1 } %m, 0
  %ov0 = extractvalue { i64, i1 } %m, 1
  br i1 %ov0, label %bad, label %add1
add1:
  %a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %rows, i64 1)
  %words = extractvalue { i64, i1 } %a, 0
  %ov1 = extractvalue { i64, i1 } %a, 1
  br i1 %ov1, label %bad, label %shl
shl:
  %huge = icmp ugt i64 %words, 2305843009213693951
  br i1 %huge, label %bad, label %ok
ok:
  %bytes = shl i64 %words, 3
  ret i64 %bytes
bad:
  call void @rt_fail(ptr @.rt.slots_overflow)
  unreachable
}

; Bytes for `cap + 1` flag words, or fail on overflow.
define internal i64 @rt_slots_flag_bytes(i64 %cap) {
entry:
  %a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %cap, i64 1)
  %words = extractvalue { i64, i1 } %a, 0
  %ov = extractvalue { i64, i1 } %a, 1
  br i1 %ov, label %bad, label %shl
shl:
  %huge = icmp ugt i64 %words, 2305843009213693951
  br i1 %huge, label %bad, label %ok
ok:
  %bytes = shl i64 %words, 3
  ret i64 %bytes
bad:
  call void @rt_fail(ptr @.rt.slots_overflow)
  unreachable
}

; Bytes for a header of `5 + sn` words, or fail on overflow.
define internal i64 @rt_slots_header_bytes(i64 %sn) {
entry:
  %a = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %sn, i64 5)
  %words = extractvalue { i64, i1 } %a, 0
  %ov = extractvalue { i64, i1 } %a, 1
  br i1 %ov, label %bad, label %shl
shl:
  %huge = icmp ugt i64 %words, 2305843009213693951
  br i1 %huge, label %bad, label %ok
ok:
  %bytes = shl i64 %words, 3
  ret i64 %bytes
bad:
  call void @rt_fail(ptr @.rt.slots_overflow)
  unreachable
}

; The flags from slot `from` up to `to` are cleared and their marks are the
; `mn` words at `m0`.
define internal void @rt_slots_init(ptr %h, i64 %from, i64 %to, i64 %mn, ptr %m0) {
entry:
  %flagsp = getelementptr i64, ptr %h, i64 2
  %fl = load ptr, ptr %flagsp
  %marksp = getelementptr i64, ptr %h, i64 3
  %marks = load ptr, ptr %marksp
  %ip = alloca i64
  store i64 %from, ptr %ip
  br label %head
head:
  %i = load i64, ptr %ip
  %more = icmp ult i64 %i, %to
  br i1 %more, label %body, label %done
body:
  %fp = getelementptr i64, ptr %fl, i64 %i
  store i64 0, ptr %fp
  %off = mul i64 %i, %mn
  %mp = getelementptr i64, ptr %marks, i64 %off
  %size = shl i64 %mn, 3
  call void @llvm.memcpy.p0.p0.i64(ptr %mp, ptr %m0, i64 %size, i1 false)
  %next = add i64 %i, 1
  store i64 %next, ptr %ip
  br label %head
done:
  ret void
}

; `cap` empty slots of `n` words, each marked with the `mn` words at `m0`, in
; the state of the `sn` words at `s0`.
define internal ptr @rt_slots_new(i64 %cap, i64 %n, i64 %mn, i64 %sn, ptr %s0, ptr %m0) {
entry:
  %hb = call i64 @rt_slots_header_bytes(i64 %sn)
  %h = call ptr @rt_alloc(i64 %hb)
  %db = call i64 @rt_slots_row_bytes(i64 %cap, i64 %n)
  %data = call ptr @rt_alloc(i64 %db)
  store ptr %data, ptr %h
  %capp = getelementptr i64, ptr %h, i64 1
  store i64 %cap, ptr %capp
  %fb = call i64 @rt_slots_flag_bytes(i64 %cap)
  %fl = call ptr @rt_alloc(i64 %fb)
  %flagsp = getelementptr i64, ptr %h, i64 2
  store ptr %fl, ptr %flagsp
  %mb = call i64 @rt_slots_row_bytes(i64 %cap, i64 %mn)
  %marks = call ptr @rt_alloc(i64 %mb)
  %marksp = getelementptr i64, ptr %h, i64 3
  store ptr %marks, ptr %marksp
  %vb = call i64 @rt_slots_row_bytes(i64 1, i64 %mn)
  %vac = call ptr @rt_alloc(i64 %vb)
  %msize = shl i64 %mn, 3
  call void @llvm.memcpy.p0.p0.i64(ptr %vac, ptr %m0, i64 %msize, i1 false)
  %vacp = getelementptr i64, ptr %h, i64 4
  store ptr %vac, ptr %vacp
  %sp = getelementptr i64, ptr %h, i64 5
  %ssize = shl i64 %sn, 3
  call void @llvm.memcpy.p0.p0.i64(ptr %sp, ptr %s0, i64 %ssize, i1 false)
  call void @rt_slots_init(ptr %h, i64 0, i64 %cap, i64 %mn, ptr %m0)
  ret ptr %h
}

; Room for `cap` slots: the slots below the old capacity as they are, the new
; ones empty and marked with the `mn` words at `m0`. A smaller capacity keeps
; the heap room it had and only stores the new capacity; the caller has already
; dropped the elements of the slots that fall off. The vacant mark becomes `m0`.
define internal void @rt_slots_resize(ptr %h, i64 %cap, i64 %n, i64 %mn, ptr %m0) {
entry:
  %capp = getelementptr i64, ptr %h, i64 1
  %old = load i64, ptr %capp
  %grow = icmp ult i64 %old, %cap
  br i1 %grow, label %bigger, label %shrink_or_same
bigger:
  %db = call i64 @rt_slots_row_bytes(i64 %cap, i64 %n)
  %data0 = load ptr, ptr %h
  %data = call ptr @rt_realloc(ptr %data0, i64 %db)
  store ptr %data, ptr %h
  %fb = call i64 @rt_slots_flag_bytes(i64 %cap)
  %flagsp = getelementptr i64, ptr %h, i64 2
  %fl0 = load ptr, ptr %flagsp
  %fl = call ptr @rt_realloc(ptr %fl0, i64 %fb)
  store ptr %fl, ptr %flagsp
  %mb = call i64 @rt_slots_row_bytes(i64 %cap, i64 %mn)
  %marksp = getelementptr i64, ptr %h, i64 3
  %marks0 = load ptr, ptr %marksp
  %marks = call ptr @rt_realloc(ptr %marks0, i64 %mb)
  store ptr %marks, ptr %marksp
  store i64 %cap, ptr %capp
  call void @rt_slots_init(ptr %h, i64 %old, i64 %cap, i64 %mn, ptr %m0)
  br label %vacant
shrink_or_same:
  store i64 %cap, ptr %capp
  br label %vacant
vacant:
  %vacp = getelementptr i64, ptr %h, i64 4
  %vac = load ptr, ptr %vacp
  %msize = shl i64 %mn, 3
  call void @llvm.memcpy.p0.p0.i64(ptr %vac, ptr %m0, i64 %msize, i1 false)
  ret void
}

; The address of the room of the element of slot `i`, after a range check.
define internal ptr @rt_slots_elem(ptr %h, i64 %i, i64 %n) {
entry:
  %capp = getelementptr i64, ptr %h, i64 1
  %cap = load i64, ptr %capp
  %ok = icmp ult i64 %i, %cap
  br i1 %ok, label %go, label %bad
go:
  %data = load ptr, ptr %h
  %off = mul i64 %i, %n
  %p = getelementptr i64, ptr %data, i64 %off
  ret ptr %p
bad:
  call void @rt_fail(ptr @.rt.slots_oob)
  unreachable
}

; The address of the mark of slot `i`, or of the vacant mark when `i` is past
; the capacity.
define internal ptr @rt_slots_mark(ptr %h, i64 %i, i64 %mn) {
entry:
  %capp = getelementptr i64, ptr %h, i64 1
  %cap = load i64, ptr %capp
  %ok = icmp ult i64 %i, %cap
  br i1 %ok, label %in, label %oob
in:
  %marksp = getelementptr i64, ptr %h, i64 3
  %marks = load ptr, ptr %marksp
  %off = mul i64 %i, %mn
  %p = getelementptr i64, ptr %marks, i64 %off
  ret ptr %p
oob:
  %vacp = getelementptr i64, ptr %h, i64 4
  %vac = load ptr, ptr %vacp
  ret ptr %vac
}

; The address of the flag of slot `i`, after a range check.
define internal ptr @rt_slots_flag(ptr %h, i64 %i) {
entry:
  %capp = getelementptr i64, ptr %h, i64 1
  %cap = load i64, ptr %capp
  %ok = icmp ult i64 %i, %cap
  br i1 %ok, label %go, label %bad
go:
  %flagsp = getelementptr i64, ptr %h, i64 2
  %fl = load ptr, ptr %flagsp
  %p = getelementptr i64, ptr %fl, i64 %i
  ret ptr %p
bad:
  call void @rt_fail(ptr @.rt.slots_oob)
  unreachable
}

; Fail when slot `i` holds no element.
define internal void @rt_slots_require_full(ptr %h, i64 %i) {
entry:
  %fp = call ptr @rt_slots_flag(ptr %h, i64 %i)
  %f = load i64, ptr %fp
  %full = icmp ne i64 %f, 0
  br i1 %full, label %ok, label %bad
ok:
  ret void
bad:
  call void @rt_fail(ptr @.rt.slots_empty)
  unreachable
}

; The room, the flags, the marks, the vacant mark and the header are released:
; each element has been dropped already.
define internal void @rt_slots_free(ptr %h) {
entry:
  %data = load ptr, ptr %h
  call void @rt_free(ptr %data)
  %flagsp = getelementptr i64, ptr %h, i64 2
  %fl = load ptr, ptr %flagsp
  call void @rt_free(ptr %fl)
  %marksp = getelementptr i64, ptr %h, i64 3
  %marks = load ptr, ptr %marksp
  call void @rt_free(ptr %marks)
  %vacp = getelementptr i64, ptr %h, i64 4
  %vac = load ptr, ptr %vacp
  call void @rt_free(ptr %vac)
  call void @rt_free(ptr %h)
  ret void
}

; The digits of `v` in `base`, the last of them just before `end`: the address
; of the first.
define internal ptr @rt_digits(ptr %end, i64 %v, i64 %base) {
entry:
  %pp = alloca ptr
  %vp = alloca i64
  store ptr %end, ptr %pp
  store i64 %v, ptr %vp
  br label %body
body:
  %v0 = load i64, ptr %vp
  %d = urem i64 %v0, %base
  %q = udiv i64 %v0, %base
  store i64 %q, ptr %vp
  %p0 = load ptr, ptr %pp
  %p1 = getelementptr i8, ptr %p0, i64 -1
  store ptr %p1, ptr %pp
  %dec = icmp ult i64 %d, 10
  br i1 %dec, label %num, label %alpha
num:
  %c0 = add i64 %d, 48
  %c0b = trunc i64 %c0 to i8
  store i8 %c0b, ptr %p1
  br label %next
alpha:
  %c1 = add i64 %d, 87
  %c1b = trunc i64 %c1 to i8
  store i8 %c1b, ptr %p1
  br label %next
next:
  %more = icmp ne i64 %q, 0
  br i1 %more, label %body, label %done
done:
  %r = load ptr, ptr %pp
  ret ptr %r
}

; The number written in decimal at the end of the 32 bytes at `buf`, and
; where its first byte is, counted from `buf`.
define internal i64 @rt_fmt_u64(ptr %buf, i64 %v) {
entry:
  %end = getelementptr i8, ptr %buf, i64 32
  %start = call ptr @rt_digits(ptr %end, i64 %v, i64 10)
  %s = ptrtoint ptr %start to i64
  %b = ptrtoint ptr %buf to i64
  %off = sub i64 %s, %b
  ret i64 %off
}

; The same for a signed number, with `-` before a negative one.
define internal i64 @rt_fmt_i64(ptr %buf, i64 %v) {
entry:
  %neg = icmp slt i64 %v, 0
  br i1 %neg, label %minus, label %plus
minus:
  %mag = sub i64 0, %v
  %off = call i64 @rt_fmt_u64(ptr %buf, i64 %mag)
  %off1 = sub i64 %off, 1
  %at = getelementptr i8, ptr %buf, i64 %off1
  store i8 45, ptr %at
  ret i64 %off1
plus:
  %offp = call i64 @rt_fmt_u64(ptr %buf, i64 %v)
  ret i64 %offp
}

; The bytes of a string ended by a zero byte.
define internal i64 @rt_strlen(ptr %s) {
entry:
  %ip = alloca i64
  store i64 0, ptr %ip
  br label %head
head:
  %i = load i64, ptr %ip
  %at = getelementptr i8, ptr %s, i64 %i
  %c = load i8, ptr %at
  %end = icmp eq i8 %c, 0
  br i1 %end, label %done, label %next
next:
  %i1 = add i64 %i, 1
  store i64 %i1, ptr %ip
  br label %head
done:
  ret i64 %i
}

; A copy of a string ended by a zero byte.
define internal ptr @rt_strdup(ptr %s) {
entry:
  %n = call i64 @rt_strlen(ptr %s)
  %n1 = add i64 %n, 1
  %p = call ptr @rt_alloc(i64 %n1)
  call void @llvm.memcpy.p0.p0.i64(ptr %p, ptr %s, i64 %n1, i1 false)
  ret ptr %p
}

; What the program writes to the standard output waits here until it is full,
; a run ends or the program asks for it to be written out.
@rt.out = internal global [8192 x i8] zeroinitializer
@rt.outn = internal global i64 0

; All `n` bytes at `p` are written to the file `fd`. A failed write stops
; the loop: the run goes on, as a closed output does for the other backends.
define internal void @rt_write_all(i32 %fd, ptr %p, i64 %n) {
entry:
  %ip = alloca i64
  store i64 0, ptr %ip
  br label %head
head:
  %i = load i64, ptr %ip
  %more = icmp ult i64 %i, %n
  br i1 %more, label %body, label %done
body:
  %q = getelementptr i8, ptr %p, i64 %i
  %left = sub i64 %n, %i
  %w = call i64 @sys_write(i32 %fd, ptr %q, i64 %left)
  %intr = icmp eq i64 %w, -4
  br i1 %intr, label %head, label %check
check:
  %ok = icmp sgt i64 %w, 0
  br i1 %ok, label %step, label %done
step:
  %i1 = add i64 %i, %w
  store i64 %i1, ptr %ip
  br label %head
done:
  ret void
}

define internal void @rt_flush() {
entry:
  %n = load i64, ptr @rt.outn
  store i64 0, ptr @rt.outn
  call void @rt_write_all(i32 1, ptr @rt.out, i64 %n)
  ret void
}

; The `n` bytes at `p` are written to the standard output after what was
; written before.
define internal void @rt_out(ptr %p, i64 %n) {
entry:
  %big = icmp uge i64 %n, 8192
  br i1 %big, label %direct, label %buffered
direct:
  call void @rt_flush()
  call void @rt_write_all(i32 1, ptr %p, i64 %n)
  ret void
buffered:
  %len = load i64, ptr @rt.outn
  %after = add i64 %len, %n
  %fits = icmp ule i64 %after, 8192
  br i1 %fits, label %copy, label %spill
spill:
  call void @rt_flush()
  br label %copy
copy:
  %len2 = load i64, ptr @rt.outn
  %at = getelementptr i8, ptr @rt.out, i64 %len2
  call void @llvm.memcpy.p0.p0.i64(ptr %at, ptr %p, i64 %n, i1 false)
  %len3 = add i64 %len2, %n
  store i64 %len3, ptr @rt.outn
  ret void
}

; `show` with no handler: a line `name = text`, and the text is released.
define internal void @rt_show(ptr %name, ptr %s) {
entry:
  %nn = call i64 @rt_strlen(ptr %name)
  call void @rt_out(ptr %name, i64 %nn)
  call void @rt_out(ptr @.rt.eq, i64 3)
  %ns = call i64 @rt_strlen(ptr %s)
  call void @rt_out(ptr %s, i64 %ns)
  call void @rt_out(ptr @.rt.nl, i64 1)
  call void @rt_free(ptr %s)
  ret void
}

; `stdout`: the bytes of a `Text` are written to the standard output, all
; of them, and the value is released.
define internal void @rt_stdout(ptr %t) {
entry:
  %np = getelementptr i64, ptr %t, i64 1
  %n = load i64, ptr %np
  %b = getelementptr i8, ptr %t, i64 16
  call void @rt_out(ptr %b, i64 %n)
  call void @rt_text_drop(ptr %t)
  ret void
}

; `stdout_flush`: what is held is written out.
define internal void @rt_stdout_flush() {
entry:
  call void @rt_flush()
  ret void
}

; `hash_seed`: the words of the seed of the run, which the system picks the
; first time it is asked for: the first word for 0, the second for 1.
@.rt.seed = internal global [2 x i64] zeroinitializer
@.rt.seeded = internal global i64 0

define internal i64 @rt_hash_seed(i64 %which) {
entry:
  %done = load i64, ptr @.rt.seeded
  %have = icmp ne i64 %done, 0
  br i1 %have, label %read, label %pick
pick:
  call void @sys_random(ptr @.rt.seed, i64 16)
  store i64 1, ptr @.rt.seeded
  br label %read
read:
  %at = getelementptr i64, ptr @.rt.seed, i64 %which
  %v = load i64, ptr %at
  ret i64 %v
}

; `stderr`: the bytes of a `Text` are written to the standard error, and the
; value is released.
define internal void @rt_stderr(ptr %t) {
entry:
  %np = getelementptr i64, ptr %t, i64 1
  %n = load i64, ptr %np
  %b = getelementptr i8, ptr %t, i64 16
  call void @rt_write_all(i32 2, ptr %b, i64 %n)
  call void @rt_text_drop(ptr %t)
  ret void
}

; `exit`: what is held is written out and the run ends with the code.
define internal void @rt_exit(i64 %c) noreturn {
entry:
  call void @rt_flush()
  %c32 = trunc i64 %c to i32
  call void @sys_exit(i32 %c32)
  unreachable
}

@.rt.e2 = private unnamed_addr constant [26 x i8] c"No such file or directory\00"
@.rt.e13 = private unnamed_addr constant [18 x i8] c"Permission denied\00"
@.rt.e17 = private unnamed_addr constant [12 x i8] c"File exists\00"
@.rt.e20 = private unnamed_addr constant [16 x i8] c"Not a directory\00"
@.rt.e21 = private unnamed_addr constant [15 x i8] c"Is a directory\00"
@.rt.e39 = private unnamed_addr constant [20 x i8] c"Directory not empty\00"
@.rt.e0 = private unnamed_addr constant [14 x i8] c"Unknown error\00"
@.rt.oserr = private unnamed_addr constant [12 x i8] c" (os error \00"
@.rt.close = private unnamed_addr constant [2 x i8] c")\00"

; The text the host gives of the error number `e` of a failed system call.
define internal ptr @rt_errno_text(i64 %e) {
entry:
  %sp = alloca ptr
  store ptr @.rt.e0, ptr %sp
  switch i64 %e, label %fmt [ i64 2, label %e2 i64 13, label %e13 i64 17, label %e17 i64 20, label %e20 i64 21, label %e21 i64 39, label %e39 ]
e2:
  store ptr @.rt.e2, ptr %sp
  br label %fmt
e13:
  store ptr @.rt.e13, ptr %sp
  br label %fmt
e17:
  store ptr @.rt.e17, ptr %sp
  br label %fmt
e20:
  store ptr @.rt.e20, ptr %sp
  br label %fmt
e21:
  store ptr @.rt.e21, ptr %sp
  br label %fmt
e39:
  store ptr @.rt.e39, ptr %sp
  br label %fmt
fmt:
  %s = load ptr, ptr %sp
  %n = call i64 @rt_strlen(ptr %s)
  %t1 = call ptr @rt_text(ptr %s, i64 %n)
  %t2 = call ptr @rt_text(ptr @.rt.oserr, i64 11)
  %t3 = call ptr @rt_text_concat(ptr %t1, ptr %t2)
  %t4 = call ptr @rt_text_of_u64(i64 %e)
  %t5 = call ptr @rt_text_concat(ptr %t3, ptr %t4)
  %t6 = call ptr @rt_text(ptr @.rt.close, i64 1)
  %t7 = call ptr @rt_text_concat(ptr %t5, ptr %t6)
  call void @rt_text_drop(ptr %t1)
  call void @rt_text_drop(ptr %t2)
  call void @rt_text_drop(ptr %t3)
  call void @rt_text_drop(ptr %t4)
  call void @rt_text_drop(ptr %t5)
  call void @rt_text_drop(ptr %t6)
  ret ptr %t7
}

; The whole file at the text `path`, as a `Text`: an error number (0 for none)
; and the text.
define internal [2 x i64] @rt_fs_read(ptr %path) {
entry:
  %p = getelementptr i8, ptr %path, i64 16
  %fd = call i64 @sys_open(ptr %p)
  %bad = icmp slt i64 %fd, 0
  br i1 %bad, label %fail, label %open
fail:
  %e = sub i64 0, %fd
  %r = insertvalue [2 x i64] zeroinitializer, i64 %e, 0
  ret [2 x i64] %r
open:
  %bp = alloca ptr
  %lp = alloca i64
  %cp = alloca i64
  %b0 = call ptr @rt_alloc(i64 4096)
  store ptr %b0, ptr %bp
  store i64 0, ptr %lp
  store i64 4096, ptr %cp
  br label %loop
loop:
  %len = load i64, ptr %lp
  %cap = load i64, ptr %cp
  %full = icmp eq i64 %len, %cap
  br i1 %full, label %grow, label %rd
grow:
  %buf0 = load ptr, ptr %bp
  %ncap = shl i64 %cap, 1
  %buf1 = call ptr @rt_realloc(ptr %buf0, i64 %ncap)
  store ptr %buf1, ptr %bp
  store i64 %ncap, ptr %cp
  br label %rd
rd:
  %len2 = load i64, ptr %lp
  %cap2 = load i64, ptr %cp
  %buf = load ptr, ptr %bp
  %at = getelementptr i8, ptr %buf, i64 %len2
  %room = sub i64 %cap2, %len2
  %n = call i64 @sys_read(i64 %fd, ptr %at, i64 %room)
  %intr = icmp eq i64 %n, -4
  br i1 %intr, label %loop, label %chk
chk:
  %err = icmp slt i64 %n, 0
  br i1 %err, label %rfail, label %more
rfail:
  %bufe = load ptr, ptr %bp
  call void @rt_free(ptr %bufe)
  %c1 = call i64 @sys_close(i64 %fd)
  %ne = sub i64 0, %n
  %re = insertvalue [2 x i64] zeroinitializer, i64 %ne, 0
  ret [2 x i64] %re
more:
  %done = icmp eq i64 %n, 0
  %len3 = add i64 %len2, %n
  store i64 %len3, ptr %lp
  br i1 %done, label %fin, label %loop
fin:
  %bufz = load ptr, ptr %bp
  %lenz = load i64, ptr %lp
  %t = call ptr @rt_text(ptr %bufz, i64 %lenz)
  call void @rt_free(ptr %bufz)
  %c2 = call i64 @sys_close(i64 %fd)
  %w = ptrtoint ptr %t to i64
  %r2 = insertvalue [2 x i64] zeroinitializer, i64 %w, 1
  ret [2 x i64] %r2
}

; A run-time error: what was shown so far is written, then the message, and
; the run ends with the exit code 1.
define internal void @rt_fail(ptr %msg) noreturn {
entry:
  call void @rt_flush()
  %n = call i64 @rt_strlen(ptr %msg)
  call void @rt_write_all(i32 2, ptr @.rt.error, i64 7)
  call void @rt_write_all(i32 2, ptr %msg, i64 %n)
  call void @rt_write_all(i32 2, ptr @.rt.nl, i64 1)
  call void @sys_exit(i32 1)
  unreachable
}
"#;

#[cfg(test)]
mod tests {
    use super::*;

    /// `totes/llvm/src/runtime.taut` holds the runtime of `Sys::Linux` as the
    /// tote writes it, in parts, each indented: the same text. The two are
    /// written by hand and kept the same here.
    #[test]
    fn the_tote_writes_the_same_runtime() {
        let tote = include_str!("../../../totes/llvm/src/runtime.taut");
        let mut text = String::new();
        let mut rest = tote;
        while let Some(open) = rest.find("ll!(```\n") {
            rest = &rest[open + "ll!(```\n".len()..];
            let close = rest
                .find("\n  ```)")
                .expect("the end of a part of the runtime");
            for line in rest[..close].lines() {
                text.push_str(line.strip_prefix("    ").unwrap_or(line));
                text.push('\n');
            }
            text.push('\n');
            rest = &rest[close..];
        }
        let squeeze = |s: &str| {
            s.lines()
                .filter(|l| !l.trim().is_empty())
                .collect::<Vec<_>>()
                .join("\n")
        };
        assert_eq!(squeeze(&text), squeeze(&runtime(Sys::Linux)));
    }

    /// The runtime reaches the system only through the layer: no call of the
    /// C library for memory or for text is left, for either system. Only the
    /// tests' `Sys::Asan` takes its blocks from `malloc`.
    #[test]
    fn runtime_calls_no_library_for_memory_or_text() {
        for sys in [Sys::Linux, Sys::Libc] {
            let text = runtime(sys);
            for name in [
                "@malloc",
                "@realloc",
                "@free",
                "@printf",
                "@snprintf",
                "@dprintf",
                "@fflush",
                "@strlen",
                "@strdup",
            ] {
                assert!(
                    !text.contains(name),
                    "{sys:?}: `{name}` is a call of the C library"
                );
            }
        }
        let text = runtime(Sys::Linux);
        for name in ["@exit", "@write", "@mmap", "@munmap"] {
            assert!(!text.contains(name), "`{name}` is a call of the C library");
        }
        assert!(runtime(Sys::Asan).contains("@malloc"));
    }
}
