#!/bin/sh
qemu-system-x86_64 --nographic -monitor /dev/null -kernel ./bzImage -initrd ./initramfs.img -m 512M -append 'console=ttyS0 rdinit=/linuxrc kaslr quiet oops=panic panic=1' -no-reboot -net none 2>/dev/null

