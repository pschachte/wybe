public type int is
    public func +(x:int,y:int):int = foreign llvm add(x,y)
    public func -(x:int,y:int):int = foreign llvm sub(x,y)
    public func *(x:int,y:int):int = foreign llvm mul(x,y)
    public func /(x:int,y:int):int = foreign llvm sdiv(x,y)
    public func ==(x:int,y:int):bool = foreign llvm icmp(eq,x,y)
    public func /=(x:int,y:int):bool = foreign llvm icmp(ne,x,y)
    public func <(x:int,y:int):bool = foreign llvm icmp(slt,x,y)
    public func <=(x:int,y:int):bool = foreign llvm icmp(sle,x,y)
    public func >(x:int,y:int):bool = foreign llvm icmp(sgt,x,y)
    public func >=(x:int,y:int):bool = foreign llvm icmp(sge,x,y)
end
