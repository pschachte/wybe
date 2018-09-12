# LPVM Instructions #

The following instructions are supported by LPVM.  These are in addition to all
the LLVM instructions.

* `foreign lpvm alloc(`*size:*`int`, `?`*struct:type*`)`  
   Allocate (at least) *size* bytes of memory and store the address in
   *struct*, which has its specified type.

* `foreign lpvm access(`*struct:type*, *offset:*`int`, `?`*member:type2*`)`  
   Access the field of type *type2* at *offset* from the address of *struct*.

* `foreign lpvm mutate(`*struct:type*, `?`*struct2:type*, *offset:*`int`,
   *member:type2*`)`  
  *struct2* is the same as *struct*, except that it has *member*, with type
 *type2*, at *offset* from the address of *struct*.

The last instruction will soon be replaced with the following:

* `foreign lpvm mutate(`*struct:type*, `?`*struct2:type*, *offset:*`int`,
   *destructive*:`bool`, *member:type2*`)`  
   *struct2* is the same as *struct*, except that it has *member*, with type
   *type2*, at *offset* from the address of *struct*.
   If *destructive* is `true`, then this instruction is permitted to
   perform the operation destructively, making *struct2* the same address
   as *struct*.

* `foreign lpvm cast(`*var1:type1*, `?`*var2:type2*`)`
  Move *var1* to *var2* converting its type from *type1* to *type2*, without
  changing the representation.  This just allows getting around LLVM strong
  typing; it does not actually require any instructions.
