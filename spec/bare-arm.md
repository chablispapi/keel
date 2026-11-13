# Proposal: a freestanding AArch64 target that boots in an Apple virtual machine

## The problem

The question was whether Keel could write an OS that boots under Apple's Virtualization.framework (VZ).
That framework only runs ARM64 guests. Keel already has these pieces:
- A freestanding RISC-V target: QEMU virt and Pico 2, with MMIO, Hart, `def interrupt` and cells.
- An AArch64 back end, but it only produces macOS Mach-O user programs linked with libc.

What's missing is a freestanding AArch64 target that VZ can load. Status: parked, nothing implemented yet.

**Key design choice:** use the arm64 Linux boot protocol. The image is a raw `Image` with the
64-byte header, entered at EL1 with the DTB pointer in `x0`. QEMU `-machine virt -kernel Image`
and VZ's `VZLinuxBootLoader` both accept it, and `vfkit` exposes the VZ loader from the
command line. So every step except the last one runs under QEMU in `cabal test all`, and VZ
becomes one manual smoke test at the end.

## Steps

### Step 0: spike (about one hour, no code)

Boot any stock arm64 Linux kernel under `vfkit` and dump its device tree
(`dtc -I fs /proc/device-tree`). Record these facts before designing anything:
- RAM base and size
- whether there is a PL011 UART or only virtio-console
- the PCIe ECAM base and BAR windows
- GIC version and addresses
- PSCI conduit (`hvc` or `smc`)
- the load address and whether `text_offset` is honoured

These facts decide steps 3 and 4. Write them at the top of this file.

### Step 1: `--target aarch64-virt` on QEMU with a PL011 UART

This mirrors `Board`/`Virt` in `ref/src/Keel/RiscV.hs`.

- **`ref/src/Keel/AArch64.hs`:** add a target parameter (`Mac | Bare`) to
  `emitProgramWithReuse` and `emitRuntime`. Bare changes only these places:
  - Section directives: replace `__TEXT`/`__DATA`/`.zerofill` (around lines 129–170) with
    ELF `.text`, `.data` and `.bss`.
  - Addressing: `@PAGE`/`@PAGEOFF` (3 uses) become `:lo12:`.
  - Startup: `_main` (around line 1527) becomes `_start`. It sets up the stack, zeroes `.bss`,
    then follows the existing `_main` body.
  - Host calls: `_printf`, `_putchar`, `_getenv` and `_dprintf` become a PL011 putc/getc at
    `0x0900_0000`, plus a small number printer. Copy the logic of RISC-V's printing routines.
  - Exit and panic: semihosting `SYS_EXIT_EXTENDED` (`hlt #0xf000`), so QEMU returns status 101.
  - Refuse `FLibm` the way `compileRiscVFor` does.

  `Keel.Runtime` routines are already shared and need nothing.
- **`ref/src/Keel/Toolchain.hs`:** add `buildArm` and `runQemuArm`, modelled on `buildRiscV`
  and `runQemu`. They use `--target=aarch64-none-elf` with the clang and lld that
  `findRiscVTools` already locates, a linker script at the QEMU virt RAM base, and
  `qemu-system-aarch64 -machine virt -cpu cortex-a72 -semihosting -nographic -kernel`.
- **`ref/app/keelc.hs`:** accept `--target aarch64-virt` in `build`, and make `qemu` dispatch on it.
- **`ref/test/Native.hs`:** run every native case on aarch64-virt as RISC-V does, with
  reference output compared and `live=0`.
- **`spec/surface.md`:** add the target line.

### Step 2: MMIO, `read16`/`write16`, Hart on bare AArch64

- **MMIO:** unhandled MMIO becomes `ldrb`/`ldrh`/`ldr w` and `strb`/`strh`/`str w`. With the
  MMU off, memory is Device-nGnRnE, so no barriers are needed.
- **`read16`/`write16`:** add them on every target and in the evaluator. virtio-pci's common
  config has 16-bit fields such as `queue_select`, and a 32-bit write would clobber the
  neighbouring field. 64-bit fields are written as two 32-bit halves, which the virtio spec allows.
- **Hart:** keep the effect and map register numbers to a small AArch64 table, the same way
  `csrs` is a table in RiscV.hs: DAIF, CNTV_CTL_EL0, CNTV_TVAL_EL0, CNTFRQ_EL0 and ESR_EL1.
  The timer needs a full write, so add `csrWrite` only when step 5 reaches it. `wfi` stays `wfi`.
- **Boot argument:** add a Hart op `bootArg() : usize` that returns the `x0` saved by `_start`
  (the DTB pointer). This is the one new built-in this plan needs.
- **Example:** port `examples/firmware/hello.kl` to a PL011 driver
  (`examples/firmware/arm/hello.kl`). It stays testable with a mocked MMIO handler.

### Step 3: a VZ-loadable `Image`

- Emit the arm64 Image header: `b _start`, `text_offset`, `image_size`, flags and the
  `ARM\x64` magic at 0x38. The linker script places it first, and the build `objcopy`s to raw binary.
- **Position independence:** VZ's load address may differ from QEMU's (step 0 tells us). Code
  is already PC-relative through `adrp` and `add`. The absolute `.quad _keel_heap` words
  (around line 153) are filled in by `_start` with `adr` instead.
- Test it by booting the same Image on QEMU through `-kernel`. QEMU recognises the header and
  passes the DTB.
- **Exit on VZ:** PSCI `SYSTEM_OFF` (`hvc #0` with `0x84000008`). Add a second board,
  `AppleVM`, which differs from `aarch64-virt` only in exit (PSCI, not semihosting) and in its
  console (step 4 if VZ has no PL011).

### Step 4: drivers, written in Keel (the "OS" part)

These go in `examples/os/` or `std/`, each tested first against a mocked MMIO handler, as
`examples/uart.kl` is:
1. **DTB parser:** big-endian walks over `read32(bootArg() + …)`. It finds memory, ECAM, GIC
   and the UART.
2. **PCIe ECAM enumeration:** find the virtio devices (vendor 0x1af4) and assign BARs.
3. **virtio-pci modern transport and virtio-console:** one RX queue and one TX queue.
   - **DMA memory:** use the last 1 MiB of RAM as reported by the DTB.
     `ponytail: fixed DMA window; a page allocator when more than one device needs queues.`
     With the MMU off, accesses are coherent with the device.
   - **QEMU test:** `-device virtio-serial-pci -device virtconsole,chardev=…`.
   - **VZ test:** `vfkit --bootloader linux,kernel=Image --device virtio-serial,stdio`.

### Step 5 (optional): interrupts

- An EL1 vector table in the runtime. On IRQ it reads `ICC_IAR1_EL1`, calls `def interrupt`
  with the INTID, writes `ICC_EOIR1_EL1` and returns with `eret`. Everything else panics with
  ESR, ELR and FAR, mirroring `_keel_trap` in RiscV.hs.
- The GICv3 distributor and redistributor are set up in Keel over MMIO, and the virtual timer
  through Hart. The example is a timer tick plus console echo, like `examples/firmware/echo.kl`.

## Deferred

MMU and caches, SMP, EL0 processes, scheduling, UEFI boot, and GPU, block and net devices.
Each would get its own plan once step 4 works.

## Verification

- `cd ref && cabal test all` with `KEEL_X86_HOST` set after each step. The new aarch64-virt
  line must pass every native case, just as RISC-V does, and the suite's skip messages are
  reported as printed.
- `ref/selfhost/parser.kl` only matters if syntax changes. This plan adds no syntax, only ops
  and a target.
- Step 3: the same `Image` prints the same output on QEMU `-kernel` and under `vfkit`.
- Step 4: the driver examples pass mocked in the evaluator and live on QEMU, and run once by
  hand under vfkit.
