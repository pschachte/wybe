public type int is
    public func +(x:int,y:int):int = foreign llvm add(x,y)
    public func -(x:int,y:int):int = foreign llvm sub(x,y)
    public func *(x:int,y:int):int = foreign llvm mul(x,y)
    public func /(x:int,y:int):int = foreign llvm sdiv(x,y)
end
