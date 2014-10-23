from barf.arch.x86.x86base import X86InstructionBase
from barf.arch.x86.x86base import X86MemoryOperand
from barf.arch.x86.x86base import X86RegisterOperand

# "Data Transfer Instructions"
# ============================================================================ #
class Mov(X86InstructionBase):
    """Representation of Mov x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Mov, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Cmove(X86InstructionBase):
    """Representation of Cmove x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmove, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovz(X86InstructionBase):
    """Representation of Cmovz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovne(X86InstructionBase):
    """Representation of Cmovne x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovne, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnz(X86InstructionBase):
    """Representation of Cmovnz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmova(X86InstructionBase):
    """Representation of Cmova x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmova, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnbe(X86InstructionBase):
    """Representation of Cmovnbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovae(X86InstructionBase):
    """Representation of Cmovae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnb(X86InstructionBase):
    """Representation of Cmovnb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovb(X86InstructionBase):
    """Representation of Cmovb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnae(X86InstructionBase):
    """Representation of Cmovnae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovbe(X86InstructionBase):
    """Representation of Cmovbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovna(X86InstructionBase):
    """Representation of Cmovna x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovna, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovg(X86InstructionBase):
    """Representation of Cmovg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnle(X86InstructionBase):
    """Representation of Cmovnle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovge(X86InstructionBase):
    """Representation of Cmovge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnl(X86InstructionBase):
    """Representation of Cmovnl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovl(X86InstructionBase):
    """Representation of Cmovl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnge(X86InstructionBase):
    """Representation of Cmovnge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovle(X86InstructionBase):
    """Representation of Cmovle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovng(X86InstructionBase):
    """Representation of Cmovng x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovng, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovc(X86InstructionBase):
    """Representation of Cmovc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnc(X86InstructionBase):
    """Representation of Cmovnc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovo(X86InstructionBase):
    """Representation of Cmovo x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovo, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovno(X86InstructionBase):
    """Representation of Cmovno x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovno, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovs(X86InstructionBase):
    """Representation of Cmovs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovns(X86InstructionBase):
    """Representation of Cmovns x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovns, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovp(X86InstructionBase):
    """Representation of Cmovp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovpe(X86InstructionBase):
    """Representation of Cmovpe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovpe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovnp(X86InstructionBase):
    """Representation of Cmovnp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovnp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmovpo(X86InstructionBase):
    """Representation of Cmovpo x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmovpo, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Xchg(X86InstructionBase):
    """Representation of Xchg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Xchg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
            self.operands[1],
        ]

class Bswap(X86InstructionBase):
    """Representation of Bswap x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bswap, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Xadd(X86InstructionBase):
    """Representation of Xadd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Xadd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmpxchg(X86InstructionBase):
    """Representation of Cmpxchg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmpxchg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmpxchg8b(X86InstructionBase):
    """Representation of Cmpxchg8b x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmpxchg8b, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Push(X86InstructionBase):
    """Representation of Push x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Push, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pop(X86InstructionBase):
    """Representation of Pop x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pop, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Pusha(X86InstructionBase):
    """Representation of Pusha x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pusha, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pushad(X86InstructionBase):
    """Representation of Pushad x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pushad, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Popa(X86InstructionBase):
    """Representation of Popa x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Popa, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Popad(X86InstructionBase):
    """Representation of Popad x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Popad, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cwd(X86InstructionBase):
    """Representation of Cwd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cwd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cdq(X86InstructionBase):
    """Representation of Cdq x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cdq, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cbw(X86InstructionBase):
    """Representation of Cbw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cbw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cwde(X86InstructionBase):
    """Representation of Cwde x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cwde, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movsx(X86InstructionBase):
    """Representation of Movsx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movsx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movzx(X86InstructionBase):
    """Representation of Movzx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movzx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[1], True),
        ]


    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

# "Binary Arithmetic Instructions"
# ============================================================================ #
class Add(X86InstructionBase):
    """Representation of Add x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Add, self).__init__(prefix, mnemonic, operands, architecture_mode)

        self._flags_affected = ["OF", "SF", "ZF", "AF", "CF", "PF"]

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]


class Adc(X86InstructionBase):
    """Representation of Adc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Adc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Sub(X86InstructionBase):
    """Representation of Sub x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sub, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Sbb(X86InstructionBase):
    """Representation of Sbb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sbb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Imul(X86InstructionBase):
    """Representation of Imul x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Imul, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        if len(self.operands) == 1:

            if self.operands[0].size == 8:

                return [
                    (self.operands[0], True),
                    (X86RegisterOperand("al", 8), True),
                ]

            elif self.operands[0].size == 16:

                return [
                    (self.operands[0], True),
                    (X86RegisterOperand("ax", 16), True),
                ]

            elif self.operands[0].size == 32:

                return [
                    (self.operands[0], True),
                    (X86RegisterOperand("eax", 32), True),
                ]

            elif self.operands[0].size == 64:

                return [
                    (self.operands[0], True),
                    (X86RegisterOperand("rax", 64), True),
                ]

            else:

                raise Exception()

        elif len(self.operands) == 2:

            return [
                (self.operands[0], True),
                (self.operands[1], True),
            ]

        elif len(self.operands) == 3:

            return [
                (self.operands[1], True),
                (self.operands[2], True),
            ]

        else:
            raise Exception()

    @property
    def destination_operands(self):
        """Get destination operands."""
        if len(self.operands) == 1:

            if self.operands[0].size == 8:

                return [
                    X86RegisterOperand("ah", 8),
                    X86RegisterOperand("al", 8),
                ]

            elif self.operands[0].size == 16:

                return [
                    X86RegisterOperand("dx", 16),
                    X86RegisterOperand("ax", 16),
                ]

            elif self.operands[0].size == 32:

                return [
                    X86RegisterOperand("edx", 32),
                    X86RegisterOperand("eax", 32),
                ]

            elif self.operands[0].size == 64:

                return [
                    X86RegisterOperand("rdx", 64),
                    X86RegisterOperand("rax", 64),
                ]

            else:

                raise Exception()

        elif len(self.operands) == 2:

            return [
                self.operands[0],
            ]

        elif len(self.operands) == 3:

            return [
                self.operands[0],
            ]

        else:
            raise Exception()

class Mul(X86InstructionBase):
    """Representation of Mul x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Mul, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        assert len(self.operands) == 1

        if self.operands[0].size == 8:

            return [
                (self.operands[0], True),
                (X86RegisterOperand("al", 8), True),
            ]

        elif self.operands[0].size == 16:

            return [
                (self.operands[0], True),
                (X86RegisterOperand("ax", 16), True),
            ]

        elif self.operands[0].size == 32:

            return [
                (self.operands[0], True),
                (X86RegisterOperand("eax", 32), True),
            ]

        elif self.operands[0].size == 64:

            return [
                (self.operands[0], True),
                (X86RegisterOperand("rax", 64), True),
            ]

        else:
            raise Exception()

    @property
    def destination_operands(self):
        """Get destination operands."""
        if self.operands[0].size == 8:

            return [
                X86RegisterOperand("ah", 8),
                X86RegisterOperand("al", 8),
            ]

        elif self.operands[0].size == 16:

            return [
                X86RegisterOperand("dx", 16),
                X86RegisterOperand("ax", 16),
            ]

        elif self.operands[0].size == 32:

            return [
                X86RegisterOperand("edx", 32),
                X86RegisterOperand("eax", 32),
            ]

        elif self.operands[0].size == 64:

            return [
                X86RegisterOperand("rdx", 64),
                X86RegisterOperand("rax", 64),
            ]

        else:
            raise Exception()

class Idiv(X86InstructionBase):
    """Representation of Idiv x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Idiv, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Div(X86InstructionBase):
    """Representation of Div x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Div, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        assert len(self.operands) == 1

        if self.operands[0].size == 8:

            return [
                (X86RegisterOperand("ah", 8), True),
                (X86RegisterOperand("al", 8), True),
                (self.operands[0], True),
            ]

        elif self.operands[0].size == 16:

            return [
                (X86RegisterOperand("dx", 16), True),
                (X86RegisterOperand("ax", 16), True),
                (self.operands[0], True),
            ]

        elif self.operands[0].size == 32:

            return [
                (X86RegisterOperand("edx", 32), True),
                (X86RegisterOperand("eax", 32), True),
                (self.operands[0], True),
            ]

        elif self.operands[0].size == 64:

            return [
                (X86RegisterOperand("rdx", 64), True),
                (X86RegisterOperand("rax", 64), True),
                (self.operands[0], True),
            ]

        else:
            raise Exception()

    @property
    def destination_operands(self):
        """Get destination operands."""
        if self.operands[0].size == 8:

            return [
                X86RegisterOperand("ah", 8),
                X86RegisterOperand("al", 8),
            ]

        elif self.operands[0].size == 16:

            return [
                X86RegisterOperand("dx", 16),
                X86RegisterOperand("ax", 16),
            ]

        elif self.operands[0].size == 32:

            return [
                X86RegisterOperand("edx", 32),
                X86RegisterOperand("eax", 32),
            ]

        elif self.operands[0].size == 64:

            return [
                X86RegisterOperand("rdx", 64),
                X86RegisterOperand("rax", 64),
            ]

        else:
            raise Exception()

class Inc(X86InstructionBase):
    """Representation of Inc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Inc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Dec(X86InstructionBase):
    """Representation of Dec x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Dec, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Neg(X86InstructionBase):
    """Representation of Neg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Neg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Cmp(X86InstructionBase):
    """Representation of Cmp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmp, self).__init__(prefix, mnemonic, operands, architecture_mode)

        # self._flags_affected = ["OF", "SF", "ZF", "AF", "CF", "PF"]
        self._flags_affected = ["ZF"]

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Decimal Arithmetic Instructions"
# ============================================================================ #
class Daa(X86InstructionBase):
    """Representation of Daa x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Daa, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Das(X86InstructionBase):
    """Representation of Das x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Das, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Aaa(X86InstructionBase):
    """Representation of Aaa x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Aaa, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Aas(X86InstructionBase):
    """Representation of Aas x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Aas, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Aam(X86InstructionBase):
    """Representation of Aam x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Aam, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Aad(X86InstructionBase):
    """Representation of Aad x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Aad, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Logical Instructions"
# ============================================================================ #
class And(X86InstructionBase):
    """Representation of And x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(And, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Or(X86InstructionBase):
    """Representation of Or x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Or, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Xor(X86InstructionBase):
    """Representation of Xor x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Xor, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Not(X86InstructionBase):
    """Representation of Not x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Not, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

# "Shift and Rotate Instructions"
# ============================================================================ #
class Sar(X86InstructionBase):
    """Representation of Sar x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sar, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Shr(X86InstructionBase):
    """Representation of Shr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Sal(X86InstructionBase):
    """Representation of Sal x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sal, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Shl(X86InstructionBase):
    """Representation of Shl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Shrd(X86InstructionBase):
    """Representation of Shrd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shrd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Shld(X86InstructionBase):
    """Representation of Shld x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shld, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ror(X86InstructionBase):
    """Representation of Ror x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ror, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Rol(X86InstructionBase):
    """Representation of Rol x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rol, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Rcr(X86InstructionBase):
    """Representation of Rcr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rcr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Rcl(X86InstructionBase):
    """Representation of Rcl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rcl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Bit and Byte Instructions"
# ============================================================================ #
class Bt(X86InstructionBase):
    """Representation of Bt x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bt, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bts(X86InstructionBase):
    """Representation of Bts x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bts, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Btr(X86InstructionBase):
    """Representation of Btr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Btr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Btc(X86InstructionBase):
    """Representation of Btc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Btc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bsf(X86InstructionBase):
    """Representation of Bsf x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bsf, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bsr(X86InstructionBase):
    """Representation of Bsr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bsr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Sete(X86InstructionBase):
    """Representation of Sete x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sete, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setz(X86InstructionBase):
    """Representation of Setz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setne(X86InstructionBase):
    """Representation of Setne x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setne, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnz(X86InstructionBase):
    """Representation of Setnz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Seta(X86InstructionBase):
    """Representation of Seta x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Seta, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnbe(X86InstructionBase):
    """Representation of Setnbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setae(X86InstructionBase):
    """Representation of Setae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnb(X86InstructionBase):
    """Representation of Setnb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnc(X86InstructionBase):
    """Representation of Setnc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setb(X86InstructionBase):
    """Representation of Setb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnae(X86InstructionBase):
    """Representation of Setnae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setc(X86InstructionBase):
    """Representation of Setc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setbe(X86InstructionBase):
    """Representation of Setbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setna(X86InstructionBase):
    """Representation of Setna x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setna, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setg(X86InstructionBase):
    """Representation of Setg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnle(X86InstructionBase):
    """Representation of Setnle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setge(X86InstructionBase):
    """Representation of Setge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnl(X86InstructionBase):
    """Representation of Setnl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setl(X86InstructionBase):
    """Representation of Setl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnge(X86InstructionBase):
    """Representation of Setnge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setle(X86InstructionBase):
    """Representation of Setle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setng(X86InstructionBase):
    """Representation of Setng x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setng, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Sets(X86InstructionBase):
    """Representation of Sets x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sets, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setns(X86InstructionBase):
    """Representation of Setns x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setns, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Seto(X86InstructionBase):
    """Representation of Seto x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Seto, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setno(X86InstructionBase):
    """Representation of Setno x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setno, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setpe(X86InstructionBase):
    """Representation of Setpe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setpe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setp(X86InstructionBase):
    """Representation of Setp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setpo(X86InstructionBase):
    """Representation of Setpo x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setpo, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Setnp(X86InstructionBase):
    """Representation of Setnp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Setnp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Test(X86InstructionBase):
    """Representation of Test x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Test, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
            (self.operands[1], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Control Transfer Instructions"
# ============================================================================ #
class Jmp(X86InstructionBase):
    """Representation of Jmp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jmp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Je(X86InstructionBase):
    """Representation of Je x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Je, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jz(X86InstructionBase):
    """Representation of Jz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jne(X86InstructionBase):
    """Representation of Jne x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jne, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnz(X86InstructionBase):
    """Representation of Jnz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ja(X86InstructionBase):
    """Representation of Ja x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ja, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnbe(X86InstructionBase):
    """Representation of Jnbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jae(X86InstructionBase):
    """Representation of Jae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnb(X86InstructionBase):
    """Representation of Jnb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jb(X86InstructionBase):
    """Representation of Jb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnae(X86InstructionBase):
    """Representation of Jnae x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnae, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jbe(X86InstructionBase):
    """Representation of Jbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jna(X86InstructionBase):
    """Representation of Jna x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jna, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jg(X86InstructionBase):
    """Representation of Jg x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jg, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnle(X86InstructionBase):
    """Representation of Jnle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jge(X86InstructionBase):
    """Representation of Jge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnl(X86InstructionBase):
    """Representation of Jnl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jl(X86InstructionBase):
    """Representation of Jl x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jl, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnge(X86InstructionBase):
    """Representation of Jnge x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnge, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jle(X86InstructionBase):
    """Representation of Jle x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jle, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jng(X86InstructionBase):
    """Representation of Jng x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jng, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jc(X86InstructionBase):
    """Representation of Jc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnc(X86InstructionBase):
    """Representation of Jnc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jo(X86InstructionBase):
    """Representation of Jo x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jo, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jno(X86InstructionBase):
    """Representation of Jno x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jno, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Js(X86InstructionBase):
    """Representation of Js x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Js, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jns(X86InstructionBase):
    """Representation of Jns x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jns, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jpo(X86InstructionBase):
    """Representation of Jpo x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jpo, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jnp(X86InstructionBase):
    """Representation of Jnp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jnp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jpe(X86InstructionBase):
    """Representation of Jpe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jpe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jp(X86InstructionBase):
    """Representation of Jp x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jp, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jcxz(X86InstructionBase):
    """Representation of Jcxz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jcxz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Jecxz(X86InstructionBase):
    """Representation of Jecxz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Jecxz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Loop(X86InstructionBase):
    """Representation of Loop x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Loop, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Loopz(X86InstructionBase):
    """Representation of Loopz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Loopz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Loope(X86InstructionBase):
    """Representation of Loope x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Loope, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Loopnz(X86InstructionBase):
    """Representation of Loopnz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Loopnz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Loopne(X86InstructionBase):
    """Representation of Loopne x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Loopne, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Call(X86InstructionBase):
    """Representation of Call x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Call, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[0], True),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ret(X86InstructionBase):
    """Representation of Ret x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ret, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Iret(X86InstructionBase):
    """Representation of Iret x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Iret, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Iretd(X86InstructionBase):
    """Representation of Iretd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Iretd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Int(X86InstructionBase):
    """Representation of Int x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Int, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Into(X86InstructionBase):
    """Representation of Into x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Into, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bound(X86InstructionBase):
    """Representation of Bound x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bound, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "String Instructions"
# ============================================================================ #
class Movs(X86InstructionBase):
    """Representation of Movs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movsb(X86InstructionBase):
    """Representation of Movsb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movsb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        if len(self.operands) == 0:

            return [
                (X86MemoryOperand("ds", "esi", None, None, 0x0), False),
            ]

        else:

            return [
                (self.operands[0], False),
            ]

    @property
    def destination_operands(self):
        """Get destination operands."""

        if len(self.operands) == 0:

            return [
                X86MemoryOperand("ds", "edi", None, None, 0x0),
            ]

        else:

            return [
                self.operands[1],
            ]

class Movs(X86InstructionBase):
    """Representation of Movs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movsw(X86InstructionBase):
    """Representation of Movsw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movsw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movs(X86InstructionBase):
    """Representation of Movs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movsd(X86InstructionBase):
    """Representation of Movsd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movsd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmps(X86InstructionBase):
    """Representation of Cmps x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmps, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmpsb(X86InstructionBase):
    """Representation of Cmpsb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmpsb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmps(X86InstructionBase):
    """Representation of Cmps x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmps, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmpsw(X86InstructionBase):
    """Representation of Cmpsw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmpsw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmps(X86InstructionBase):
    """Representation of Cmps x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmps, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmpsd(X86InstructionBase):
    """Representation of Cmpsd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmpsd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scas(X86InstructionBase):
    """Representation of Scas x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scas, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scasb(X86InstructionBase):
    """Representation of Scasb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scasb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scas(X86InstructionBase):
    """Representation of Scas x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scas, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scasw(X86InstructionBase):
    """Representation of Scasw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scasw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scas(X86InstructionBase):
    """Representation of Scas x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scas, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Scasd(X86InstructionBase):
    """Representation of Scasd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Scasd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lods(X86InstructionBase):
    """Representation of Lods x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lods, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lodsb(X86InstructionBase):
    """Representation of Lodsb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lodsb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lods(X86InstructionBase):
    """Representation of Lods x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lods, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lodsw(X86InstructionBase):
    """Representation of Lodsw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lodsw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lods(X86InstructionBase):
    """Representation of Lods x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lods, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lodsd(X86InstructionBase):
    """Representation of Lodsd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lodsd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stos(X86InstructionBase):
    """Representation of Stos x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stos, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stosb(X86InstructionBase):
    """Representation of Stosb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stosb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stos(X86InstructionBase):
    """Representation of Stos x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stos, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stosw(X86InstructionBase):
    """Representation of Stosw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stosw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stos(X86InstructionBase):
    """Representation of Stos x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stos, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Stosd(X86InstructionBase):
    """Representation of Stosd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stosd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Rep(X86InstructionBase):
    """Representation of Rep x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rep, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Repe(X86InstructionBase):
    """Representation of Repe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Repe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Repz(X86InstructionBase):
    """Representation of Repz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Repz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Repne(X86InstructionBase):
    """Representation of Repne x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Repne, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Repnz(X86InstructionBase):
    """Representation of Repnz x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Repnz, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "I/O Instructions"
# ============================================================================ #
class In(X86InstructionBase):
    """Representation of In x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(In, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Out(X86InstructionBase):
    """Representation of Out x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Out, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ins(X86InstructionBase):
    """Representation of Ins x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ins, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Insb(X86InstructionBase):
    """Representation of Insb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Insb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ins(X86InstructionBase):
    """Representation of Ins x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ins, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Insw(X86InstructionBase):
    """Representation of Insw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Insw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ins(X86InstructionBase):
    """Representation of Ins x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ins, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Insd(X86InstructionBase):
    """Representation of Insd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Insd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outs(X86InstructionBase):
    """Representation of Outs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outsb(X86InstructionBase):
    """Representation of Outsb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outsb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outs(X86InstructionBase):
    """Representation of Outs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outsw(X86InstructionBase):
    """Representation of Outsw x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outsw, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outs(X86InstructionBase):
    """Representation of Outs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Outsd(X86InstructionBase):
    """Representation of Outsd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Outsd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Enter and Leave Instructions"
# ============================================================================ #
class Enter(X86InstructionBase):
    """Representation of Enter x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Enter, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Leave(X86InstructionBase):
    """Representation of Leave x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Leave, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Flag Control (EFLAG) Instructions"
# ============================================================================ #
class Stc(X86InstructionBase):
    """Representation of Stc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Stc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Clc(X86InstructionBase):
    """Representation of Clc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Clc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cmc(X86InstructionBase):
    """Representation of Cmc x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cmc, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cld(X86InstructionBase):
    """Representation of Cld x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cld, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Std(X86InstructionBase):
    """Representation of Std x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Std, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lahf(X86InstructionBase):
    """Representation of Lahf x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lahf, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Sahf(X86InstructionBase):
    """Representation of Sahf x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sahf, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pushf(X86InstructionBase):
    """Representation of Pushf x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pushf, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pushfd(X86InstructionBase):
    """Representation of Pushfd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pushfd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Popf(X86InstructionBase):
    """Representation of Popf x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Popf, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Popfd(X86InstructionBase):
    """Representation of Popfd x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Popfd, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Sti(X86InstructionBase):
    """Representation of Sti x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sti, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cli(X86InstructionBase):
    """Representation of Cli x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cli, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Segment Register Instructions"
# ============================================================================ #
class Lds(X86InstructionBase):
    """Representation of Lds x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lds, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Les(X86InstructionBase):
    """Representation of Les x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Les, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lfs(X86InstructionBase):
    """Representation of Lfs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lfs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lgs(X86InstructionBase):
    """Representation of Lgs x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lgs, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lss(X86InstructionBase):
    """Representation of Lss x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lss, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Miscellaneous Instructions"
# ============================================================================ #
class Lea(X86InstructionBase):
    """Representation of Lea x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lea, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
            (self.operands[1], False),
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
            self.operands[0],
        ]

class Nop(X86InstructionBase):
    """Representation of Nop x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Nop, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Ud2(X86InstructionBase):
    """Representation of Ud2 x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Ud2, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Xlat(X86InstructionBase):
    """Representation of Xlat x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Xlat, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Xlatb(X86InstructionBase):
    """Representation of Xlatb x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Xlatb, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Cpuid(X86InstructionBase):
    """Representation of Cpuid x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Cpuid, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Movbe(X86InstructionBase):
    """Representation of Movbe x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Movbe, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Halt(X86InstructionBase):
    """Representation of Halt x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Halt, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Random Number Generator Instruction"
# ============================================================================ #
class Rdrand(X86InstructionBase):
    """Representation of Rdrand x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rdrand, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "BMI1, BMI2"
# ============================================================================ #
class Andn(X86InstructionBase):
    """Representation of Andn x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Andn, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bextr(X86InstructionBase):
    """Representation of Bextr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bextr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Blsi(X86InstructionBase):
    """Representation of Blsi x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Blsi, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Blsmk(X86InstructionBase):
    """Representation of Blsmk x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Blsmk, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Blsr(X86InstructionBase):
    """Representation of Blsr x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Blsr, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Bzhi(X86InstructionBase):
    """Representation of Bzhi x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Bzhi, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Lzcnt(X86InstructionBase):
    """Representation of Lzcnt x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Lzcnt, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Mulx(X86InstructionBase):
    """Representation of Mulx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Mulx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pdep(X86InstructionBase):
    """Representation of Pdep x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pdep, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Pext(X86InstructionBase):
    """Representation of Pext x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Pext, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Rorx(X86InstructionBase):
    """Representation of Rorx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Rorx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Sarx(X86InstructionBase):
    """Representation of Sarx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Sarx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Shlx(X86InstructionBase):
    """Representation of Shlx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shlx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Shrx(X86InstructionBase):
    """Representation of Shrx x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Shrx, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

class Tzcnt(X86InstructionBase):
    """Representation of Tzcnt x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Tzcnt, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]

# "Misc"
# ============================================================================ #
class Hlt(X86InstructionBase):
    """Representation of Hlt x86 instruction."""

    def __init__(self, prefix, mnemonic, operands, architecture_mode):
        super(Hlt, self).__init__(prefix, mnemonic, operands, architecture_mode)

    @property
    def source_operands(self):
        """Get source operands."""
        return [
        ]

    @property
    def destination_operands(self):
        """Get destination operands."""
        return [
        ]
