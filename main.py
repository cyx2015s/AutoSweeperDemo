import itertools
import os
import pprint
import random
import time
import math
import typing

CONSTANT = "常数"
INCLUDE_TOTAL_RESTRICTION = True
SHOW_EQUATION_GROUP = False


class MineSweeperEquation(dict):
    def __add__(self, other):
        keys = set(self.keys()) | set(other.keys())
        ret = {}
        for key in keys:
            ret[key] = self.get(key, 0) + other.get(key, 0)
            if ret[key] == 0 and key != CONSTANT:
                del ret[key]
        return MineSweeperEquation(ret)

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        return MineSweeperEquation({key: -self[key] for key in self if self[key] != 0 or key == CONSTANT})

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return (-self) + other

    def __mul__(self, other):
        return MineSweeperEquation(
            {key: other * self[key] for key in self if other * self[key] != 0 or key == CONSTANT})

    def __rmul__(self, other):
        return self * other

    def reduction(self):
        values = list(self.values())
        if len(values) == 1:
            gcd = values[0]
            if gcd == 0:
                return
        else:
            gcd = math.gcd(values[0], values[1])
            for _i in range(2, len(values)):
                gcd = math.gcd(gcd, values[_i])

        for key in self:
            self[key] //= gcd

    def solvable(self):
        _keys = [key for key in self.keys() if key != CONSTANT]
        _coefs = [self[key] for key in _keys]
        _tmp = []
        _ret = []

        if len(_keys) == 0:
            return [{}]

        for _i in range(2 ** len(_keys)):
            _tmp = list(map(int, bin(_i)[-1:1:-1].ljust(len(_keys), "0")))

            if sum(_coefs[_i] * _tmp[_i] for _i in range(len(_keys))) == self[CONSTANT]:
                _ret.append(_tmp)

        return [{_keys[_i]: _ret[_j][_i] for _i in range(len(_keys))}
                for _j in range(len(_ret))]


class UnitTile:
    def __init__(self, _x, _y, _board):
        self.board: MineSweeperBoard = _board
        self.uncovered = False
        self.has_mine = False
        self.flagged = False
        self.x = _x
        self.y = _y

    @property
    def nbr(self):
        _ret = []

        for _dx in (-1, 0, 1):
            for _dy in (-1, 0, 1):
                _nx = self.x + _dx
                _ny = self.y + _dy

                if 0 <= _nx < self.board.size_x and 0 <= _ny < self.board.size_y and \
                        (_dx != 0 or _dy != 0):
                    _ret.append(self.board.board[_nx][_ny])

        return _ret

    @property
    def number(self):
        _ret = 0

        for _nbr in self.nbr:
            if _nbr.has_mine:
                _ret += 1

        return _ret

    def uncover(self):
        self.uncovered = True

        if self.number == 0 and not self.has_mine:
            for _nbr in self.nbr:
                if not _nbr.uncovered:
                    self.board.uncover(_nbr.x, _nbr.y)


class MineSweeperBoard:
    def __init__(self, _size_x, _size_y, _mines):
        self.board = [[UnitTile(_i, _j, self) for _j in range(_size_y)] for _i in range(_size_x)]
        self.size_x = _size_x
        self.size_y = _size_y
        self.mines = _mines
        self.first = True

    def uncover(self, _x, _y):
        if self.first:
            self.first = False
            rands = []
            nbr = self.board[_x][_y].nbr

            for _i in range(self.size_x):
                for _j in range(self.size_y):
                    self.board[_i][_j].has_mine = False
                    if self.board[_i][_j] not in nbr and (_i, _j) != (_x, _y):
                        rands.append((_i, _j))

            random.shuffle(rands)

            for _i in range(min(self.mines, len(rands))):
                self.board[rands[_i][0]][rands[_i][1]].has_mine = True

        self.board[_x][_y].uncover()

    def __repr__(self):
        ret = "-" * (self.size_x + 2) + "\n  "
        for _i in range(self.size_x):
            ret += str(_i % 10)

        ret += "\n\n"

        for _j in range(self.size_y):
            ret += str(_j % 10) + " "

            for _i in range(self.size_x):
                if self.board[_i][_j].uncovered:
                    if self.board[_i][_j].has_mine:
                        ret += "@"
                    else:
                        tmp = self.board[_i][_j].number
                        if tmp > 0:
                            ret += str(tmp)
                        else:
                            ret += " "
                else:
                    if self.board[_i][_j].flagged:
                        ret += "^"
                    else:
                        ret += "_"

            ret += " " + str(_j % 10)
            ret += "\n"
        ret += "\n  "

        for _i in range(self.size_x):
            ret += str(_i % 10)

        ret += "\n"
        ret += "-" * (self.size_x + 2) + "\n"
        return ret

    def flag(self, _x, _y):
        self.board[_x][_y].flagged = True

    def del_flag(self, _x, _y):
        self.board[_x][_y].flagged = False

    def check_win(self):
        for _i in range(self.size_x):
            for _j in range(self.size_y):
                if self.board[_i][_j].uncovered and self.board[_i][_j].has_mine:
                    return "Lose"

        for _i in range(self.size_x):
            for _j in range(self.size_y):
                if not self.board[_i][_j].uncovered and not self.board[_i][_j].has_mine:
                    return "Continue"

        return "Win"


class ContradictoryError(Exception):
    pass


class RegretError(Exception):
    pass


# noinspection PyTypeChecker
class AIMineSweeper(MineSweeperBoard):
    def __init__(self, _size_x, _size_y, _mines):
        super(AIMineSweeper, self).__init__(_size_x, _size_y, _mines)
        self.solver: typing.Dict[typing.Union[str, tuple]:MineSweeperEquation] = {}
        if INCLUDE_TOTAL_RESTRICTION:
            self.solver = {CONSTANT: {}}
            self.solver[CONSTANT][CONSTANT] = _mines

            for _i in range(self.size_x):
                for _j in range(self.size_y):
                    self.solver[CONSTANT][(_i, _j)] = 1

            self.solver[CONSTANT] = MineSweeperEquation(self.solver[CONSTANT])
        self.solution = {}
        self.log = []
        self.log.append(f"{_size_x} x {_size_y}, 共 {_mines} 个雷\n")

    def uncover(self, _x, _y):
        super(AIMineSweeper, self).uncover(_x, _y)
        for _key in self.solver:
            if (_x, _y) in self.solver[_key]:
                del self.solver[_key][(_x, _y)]

        self.solver[(_x, _y)] = MineSweeperEquation({
            (nbr.x, nbr.y): 1
            for nbr in self.board[_x][_y].nbr if not nbr.uncovered and not nbr.flagged
        })

        self.solver[(_x, _y)][CONSTANT] = self.board[_x][_y].number
        for nbr in self.board[_x][_y].nbr:
            if nbr.flagged:
                self.solver[(_x, _y)][CONSTANT] -= 1

        self.solver[(_x, _y)] = MineSweeperEquation(self.solver[(_x, _y)])

    def run_once(self):
        if not self.solution:
            rands = []

            for _i, _j in itertools.product(range(self.size_x), range(self.size_y)):
                if not self.board[_i][_j].uncovered and not self.board[_i][_j].flagged:
                    rands.append((_i, _j))

            rand = random.choice(rands)
            self.log.append(f"随机翻开({rand[0]},{rand[1]})")
            self.uncover(rand[0], rand[1])
        else:
            for item in self.solution.items():
                _x, _y = item[0][0], item[0][1]

                if item[1] == 0:
                    if self.board[_x][_y].uncovered:
                        continue
                    self.log.append(f"翻开({_x},{_y})")
                    self.uncover(_x, _y)
                else:
                    if self.board[_x][_y].flagged:
                        continue
                    self.log.append(f"插旗({_x},{_y})")
                    self.flag(_x, _y)

            self.solution = {}
        self.log.append(repr(self))

    def eliminate(self):
        solver_keys = list(self.solver.keys())
        if CONSTANT in solver_keys:
            solver_keys.remove(CONSTANT)

        for _i in solver_keys:
            self.solver[_i] *= 1
            if len(self.solver[_i]) == 1:
                del self.solver[_i]

        solver_keys = list(self.solver.keys())
        if CONSTANT in solver_keys:
            solver_keys.remove(CONSTANT)

        for _i in range(len(solver_keys)):
            pivots = list((self.solver[solver_keys[_i]] + {}).keys())
            if len(pivots) < 2:
                continue
            if pivots[0] == CONSTANT:
                pivot = pivots[1]
            else:
                pivot = pivots[0]

            for _j in range(len(solver_keys)):
                if _i == _j:
                    continue
                if self.solver[solver_keys[_j]].get(pivot, 0) == 0:
                    continue

                self.solver[solver_keys[_j]] = \
                    self.solver[solver_keys[_j]] * self.solver[solver_keys[_i]][pivot] \
                    - self.solver[solver_keys[_i]] * self.solver[solver_keys[_j]].get(pivot, 0)

        for _i in solver_keys:
            self.solver[_i] *= 1
            if not self.solver[_i]:
                del self.solver[_i]

            for value in self.solver.values():
                if len(value.items()) > 8:
                    continue

                ret = value.solvable()
                if len(ret) == 1:
                    ret = ret[0]
                    for key in ret:
                        if key in self.solution:
                            if self.solution[key] != ret[key]:
                                raise ContradictoryError
                            else:
                                self.solution[key] = ret[key]
                        else:
                            self.solution[key] = ret[key]

        solver_keys = list(self.solver.keys())
        for _i in solver_keys:
            self.solver[_i] *= 1
            if len(self.solver[_i]) == 1:
                del self.solver[_i]

        for key in self.solver:
            self.solver[key].reduction()

        if SHOW_EQUATION_GROUP:
            self.log.append("方程组: ")
            for eq in self.solver.values():
                self.log.append(pprint.pformat(eq, width=11451))
            self.log.append("-" * (self.size_x + 2))

        self.log.append(time.strftime("%Y年%m月%d日 %H时%M分%S秒", time.localtime(time.time())))

    def flag(self, _x, _y):
        super(AIMineSweeper, self).flag(_x, _y)

        for key in self.solver:
            if (_x, _y) in self.solver[key].keys():
                self.solver[key][CONSTANT] -= self.solver[key][(_x, _y)]
                del self.solver[key][(_x, _y)]

    def del_flag(self, _x, _y):
        raise RegretError


board = AIMineSweeper(6, 6, 20)
while board.check_win() == "Continue":
    board.run_once()
    board.eliminate()

board.log.append(board.check_win())

for i in range(board.size_x):
    for j in range(board.size_y):
        if not board.board[i][j].uncovered:
            board.uncover(i, j)

board.log.append(repr(board))
os.chdir(os.getcwd() + "\\outputs\\")
file_name = time.strftime("%Y年%m月%d日 %H时%M分%S秒", time.localtime(time.time())) + \
            f" ({board.size_x} x {board.size_y}, {board.mines})"

with open(file_name + ".txt", "w", encoding="utf-8") as outfile:
    outfile.write("\n".join(board.log))