module privatetest is
    proc hidden print("private proc in a private module") end
    public proc semi_hidden print("public proc in a private module") end
end

public module publictest is
    proc semi_visible print("private proc in a public module") end
    public proc visible print("public proc in a public module") end
end
