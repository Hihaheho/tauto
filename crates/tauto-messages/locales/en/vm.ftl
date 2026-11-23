# Messages of the vm backend (`tauto run`, `tauto dev`).

vm-unsupported = { $place }: not supported by the vm backend: { $what }
vm-unsupported-yet = { $place }: not supported by the vm backend yet: { $what }
vm-check-ownership = --check-ownership runs on niri: leave out --backend vm
niri-violation = ownership broken: { $what }
niri-unsupported = { $entry }: not run by the ownership check yet: { $what }
llvm-refused = { $entry }: not written by the LLVM backend yet: { $what }
llvm-clang = the LLVM module is not compiled: { $what }
