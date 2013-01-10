public type int is
    public func +(x:int,y:int):int = foreign llvm add(32,x,y)
    public proc +(?x:int,y:int,z:int) ?x = foreign llvm sub(32,z,y) end
    public proc +(x:int,?y:int,z:int) ?y = foreign llvm sub(32,z,x) end
    public func -(x:int,y:int):int = foreign llvm sub(32,x,y)
    public proc -(?x:int,y:int,z:int) ?x = foreign llvm add(32,z,y) end
    public proc -(x:int,?y:int,z:int) ?y = foreign llvm sub(32,z,x) end
    public func *(x:int,y:int):int = foreign llvm mul(32,x,y)
    public func /(x:int,y:int):int = foreign llvm sdiv(32,x,y)
    public func ==(x:int,y:int):bool = foreign llvm icmp(eq,32,x,y)
    public func /=(x:int,y:int):bool = foreign llvm icmp(ne,32,x,y)
    public func <(x:int,y:int):bool = foreign llvm icmp(slt,32,x,y)
    public func <=(x:int,y:int):bool = foreign llvm icmp(sle,32,x,y)
    public func >(x:int,y:int):bool = foreign llvm icmp(sgt,32,x,y)
    public func >=(x:int,y:int):bool = foreign llvm icmp(sge,32,x,y)
end
