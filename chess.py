# -*- coding: utf-8 -*-
"""
chess.py — Complete two-player pass-and-play Chess in Pygame.
Implements all standard rules: legal-move filtering, check/checkmate/stalemate,
en passant, castling (with pass-through check), pawn promotion, pinned pieces.
"""

import pygame
import sys
import copy

# ─────────────────────────────────────────────
#  Constants
# ─────────────────────────────────────────────
WIDTH, HEIGHT = 560, 620
BOARD_SIZE     = 520
SQUARE         = BOARD_SIZE // 8
BOARD_OFFSET_X = (WIDTH - BOARD_SIZE) // 2
BOARD_OFFSET_Y = 40
FPS            = 60

# Colours
C_LIGHT   = (240, 217, 181)
C_DARK    = (181, 136,  99)
C_SELECT  = (100, 200, 100, 160)
C_MOVE    = ( 80, 160, 255, 140)
C_CHECK   = (220,  50,  50, 180)
C_BG      = ( 30,  30,  40)
C_PANEL   = ( 20,  20,  30)
C_WHITE_T = (245, 245, 245)
C_BLACK_T = ( 40,  40,  40)
C_BTN     = ( 60,  90, 160)
C_BTN_H   = ( 80, 120, 200)

# Piece constants  (colour * 10 + kind)
WHITE, BLACK = 1, 2
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 1, 2, 3, 4, 5, 6

UNICODE = {
    (WHITE, KING):   '♔', (WHITE, QUEEN):  '♕',
    (WHITE, ROOK):   '♖', (WHITE, BISHOP): '♗',
    (WHITE, KNIGHT): '♘', (WHITE, PAWN):   '♙',
    (BLACK, KING):   '♚', (BLACK, QUEEN):  '♛',
    (BLACK, ROOK):   '♜', (BLACK, BISHOP): '♝',
    (BLACK, KNIGHT): '♞', (BLACK, PAWN):   '♟',
}

# ─────────────────────────────────────────────
#  Board State
# ─────────────────────────────────────────────
def make_start_board():
    """Return 8×8 list-of-lists. Each cell is (colour, kind) or None."""
    b = [[None]*8 for _ in range(8)]
    order = [ROOK, KNIGHT, BISHOP, QUEEN, KING, BISHOP, KNIGHT, ROOK]
    for c, row_k, row_p in [(BLACK, 0, 1), (WHITE, 7, 6)]:
        for f, k in enumerate(order):
            b[row_k][f] = (c, k)
        for f in range(8):
            b[row_p][f] = (c, PAWN)
    return b


class GameState:
    def __init__(self):
        self.board       = make_start_board()
        self.turn        = WHITE
        self.ep_square   = None          # (row, col) or None
        # castling rights: [WK, WQ, BK, BQ]
        self.castling    = [True, True, True, True]
        self.status      = 'playing'     # 'playing','check','checkmate','stalemate'
        self.winner      = None
        self.move_log    = []            # list of move-description strings

    def copy(self):
        gs = GameState.__new__(GameState)
        gs.board     = [row[:] for row in self.board]
        gs.turn      = self.turn
        gs.ep_square = self.ep_square
        gs.castling  = self.castling[:]
        gs.status    = self.status
        gs.winner    = self.winner
        gs.move_log  = self.move_log[:]
        return gs


# ─────────────────────────────────────────────
#  Pseudo-legal move generation
# ─────────────────────────────────────────────
def pseudo_moves(gs, r, c):
    """Return list of (to_r, to_c) pseudo-legal destinations for piece at (r,c)."""
    piece = gs.board[r][c]
    if piece is None:
        return []
    colour, kind = piece
    moves = []

    def in_bounds(rr, cc):
        return 0 <= rr < 8 and 0 <= cc < 8

    def empty(rr, cc):
        return gs.board[rr][cc] is None

    def enemy(rr, cc):
        p = gs.board[rr][cc]
        return p is not None and p[0] != colour

    def slide(dr, dc):
        rr, cc = r + dr, c + dc
        while in_bounds(rr, cc):
            if empty(rr, cc):
                moves.append((rr, cc))
            elif enemy(rr, cc):
                moves.append((rr, cc))
                break
            else:
                break
            rr += dr; cc += dc

    if kind == PAWN:
        d = -1 if colour == WHITE else 1
        start_row = 6 if colour == WHITE else 1
        # Forward
        if in_bounds(r+d, c) and empty(r+d, c):
            moves.append((r+d, c))
            if r == start_row and empty(r+2*d, c):
                moves.append((r+2*d, c))
        # Captures
        for dc in (-1, 1):
            rr, cc = r+d, c+dc
            if in_bounds(rr, cc) and enemy(rr, cc):
                moves.append((rr, cc))
            # En passant
            if in_bounds(rr, cc) and gs.ep_square == (rr, cc):
                moves.append((rr, cc))

    elif kind == KNIGHT:
        for dr, dc in [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]:
            rr, cc = r+dr, c+dc
            if in_bounds(rr, cc) and (empty(rr,cc) or enemy(rr,cc)):
                moves.append((rr, cc))

    elif kind == BISHOP:
        for dr, dc in [(-1,-1),(-1,1),(1,-1),(1,1)]:
            slide(dr, dc)

    elif kind == ROOK:
        for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
            slide(dr, dc)

    elif kind == QUEEN:
        for dr, dc in [(-1,-1),(-1,1),(1,-1),(1,1),(-1,0),(1,0),(0,-1),(0,1)]:
            slide(dr, dc)

    elif kind == KING:
        for dr, dc in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]:
            rr, cc = r+dr, c+dc
            if in_bounds(rr, cc) and (empty(rr,cc) or enemy(rr,cc)):
                moves.append((rr, cc))
        # Castling pseudo-moves (legality checked in filter step)
        back_row = 7 if colour == WHITE else 0
        ki, qi   = (2, 0) if colour == WHITE else (2, 2)  # castling right indices
        # Kingside
        if gs.castling[ki] and r == back_row and c == 4:
            if empty(r, 5) and empty(r, 6):
                moves.append((r, 6))
        # Queenside
        if gs.castling[qi] and r == back_row and c == 4:
            if empty(r, 3) and empty(r, 2) and empty(r, 1):
                moves.append((r, 2))

    return moves


# ─────────────────────────────────────────────
#  Check detection
# ─────────────────────────────────────────────
def king_pos(board, colour):
    for r in range(8):
        for c in range(8):
            p = board[r][c]
            if p and p == (colour, KING):
                return r, c
    return None


def is_attacked(board, r, c, by_colour, ep=None):
    """True if square (r,c) is attacked by any piece of by_colour."""
    # We create a minimal gs-like object for pseudo_moves
    class _GS:
        pass
    gs = _GS()
    gs.board     = board
    gs.ep_square = ep
    gs.castling  = [False]*4

    for rr in range(8):
        for cc in range(8):
            p = board[rr][cc]
            if p and p[0] == by_colour:
                gs.board = board
                for tr, tc in pseudo_moves(gs, rr, cc):
                    if tr == r and tc == c:
                        return True
    return False


def is_in_check(colour, board, ep=None):
    """True if colour's King is in check on the given board."""
    kp = king_pos(board, colour)
    if kp is None:
        return False
    opp = BLACK if colour == WHITE else WHITE
    return is_attacked(board, kp[0], kp[1], opp, ep)


# ─────────────────────────────────────────────
#  Legal move filtering
# ─────────────────────────────────────────────
def apply_move_to_board(gs, fr, fc, tr, tc):
    """
    Apply move (fr,fc)->(tr,tc) to a COPY of gs.board and return it.
    Handles en-passant capture and castling rook movement.
    Does NOT promote (leaves pawn on 8th rank for check-testing purposes).
    """
    board = [row[:] for row in gs.board]
    piece = board[fr][fc]
    colour, kind = piece

    # En passant capture
    if kind == PAWN and gs.ep_square == (tr, tc):
        ep_pawn_row = fr   # the captured pawn is on the same row as moving pawn
        board[ep_pawn_row][tc] = None

    # Move piece
    board[tr][tc] = piece
    board[fr][fc] = None

    # Castling — move rook
    if kind == KING:
        back = 7 if colour == WHITE else 0
        if fr == back and fc == 4:
            if tc == 6:   # Kingside
                board[back][5] = board[back][7]
                board[back][7] = None
            elif tc == 2: # Queenside
                board[back][3] = board[back][0]
                board[back][0] = None

    return board


def legal_moves(gs, r, c):
    """Return list of strictly legal (tr,tc) for piece at (r,c)."""
    piece = gs.board[r][c]
    if piece is None:
        return []
    colour, kind = piece
    result = []

    for tr, tc in pseudo_moves(gs, r, c):
        # Extra castling checks — king must not pass through attacked square
        if kind == KING and abs(tc - c) == 2:
            opp = BLACK if colour == WHITE else WHITE
            back = 7 if colour == WHITE else 0
            # King currently in check?
            if is_in_check(colour, gs.board, gs.ep_square):
                continue
            # Pass-through square
            mid_c = 5 if tc == 6 else 3
            if is_attacked(gs.board, back, mid_c, opp, gs.ep_square):
                continue
            # Landing square checked after move
            nb = apply_move_to_board(gs, r, c, tr, tc)
            if is_in_check(colour, nb, None):
                continue
            result.append((tr, tc))
            continue

        # General: simulate move and verify own king not in check
        nb = apply_move_to_board(gs, r, c, tr, tc)
        if not is_in_check(colour, nb, None):
            result.append((tr, tc))

    return result


def all_legal_moves(gs, colour):
    """Return all legal moves for colour as list of (fr,fc,tr,tc)."""
    moves = []
    for r in range(8):
        for c in range(8):
            p = gs.board[r][c]
            if p and p[0] == colour:
                for tr, tc in legal_moves(gs, r, c):
                    moves.append((r, c, tr, tc))
    return moves


# ─────────────────────────────────────────────
#  Apply a full legal move to GameState
# ─────────────────────────────────────────────
def do_move(gs, fr, fc, tr, tc, promote_to=QUEEN):
    """Mutate gs by executing move. Returns True if promotion needed."""
    piece  = gs.board[fr][fc]
    colour, kind = piece
    opp    = BLACK if colour == WHITE else WHITE
    back   = 7 if colour == WHITE else 0

    # Clear en-passant square (only valid for one move)
    new_ep = None

    # En passant capture
    if kind == PAWN and gs.ep_square == (tr, tc):
        gs.board[fr][tc] = None   # remove captured pawn

    # Set new en-passant target if pawn double-push
    if kind == PAWN and abs(tr - fr) == 2:
        new_ep = ((fr + tr) // 2, tc)

    # Move piece
    gs.board[tr][tc] = piece
    gs.board[fr][fc] = None

    # Castling — move rook
    if kind == KING:
        if fc == 4 and tc == 6:   # Kingside
            gs.board[back][5] = gs.board[back][7]
            gs.board[back][7] = None
        elif fc == 4 and tc == 2: # Queenside
            gs.board[back][3] = gs.board[back][0]
            gs.board[back][0] = None
        # Revoke all castling rights for this colour
        if colour == WHITE:
            gs.castling[0] = gs.castling[1] = False
        else:
            gs.castling[2] = gs.castling[3] = False

    # Revoke castling if rook moved or was captured
    if (fr, fc) == (7, 7) or (tr, tc) == (7, 7):  gs.castling[0] = False
    if (fr, fc) == (7, 0) or (tr, tc) == (7, 0):  gs.castling[1] = False
    if (fr, fc) == (0, 7) or (tr, tc) == (0, 7):  gs.castling[2] = False
    if (fr, fc) == (0, 0) or (tr, tc) == (0, 0):  gs.castling[3] = False

    gs.ep_square = new_ep

    # Pawn promotion
    needs_promote = False
    if kind == PAWN and tr == back:
        gs.board[tr][tc] = (colour, promote_to)
        needs_promote = True

    # Switch turn
    gs.turn = opp

    # Update game status
    opp_moves = all_legal_moves(gs, opp)
    in_chk    = is_in_check(opp, gs.board, gs.ep_square)

    if not opp_moves:
        if in_chk:
            gs.status = 'checkmate'
            gs.winner = colour
        else:
            gs.status = 'stalemate'
    elif in_chk:
        gs.status = 'check'
    else:
        gs.status = 'playing'

    return needs_promote


# ─────────────────────────────────────────────
#  Promotion overlay helpers
# ─────────────────────────────────────────────
PROMO_PIECES = [QUEEN, ROOK, BISHOP, KNIGHT]
PROMO_LABELS = {QUEEN: 'Queen', ROOK: 'Rook', BISHOP: 'Bishop', KNIGHT: 'Knight'}


# ─────────────────────────────────────────────
#  Rendering helpers
# ─────────────────────────────────────────────
def sq_to_pixel(r, c, flipped=False):
    """Top-left pixel of board square (r,c), respecting board orientation."""
    dr = 7 - r if flipped else r
    dc = 7 - c if flipped else c
    return (BOARD_OFFSET_X + dc * SQUARE, BOARD_OFFSET_Y + dr * SQUARE)


def pixel_to_sq(px, py, flipped=False):
    """Board square (r,c) from pixel, or None if outside board."""
    dc = (px - BOARD_OFFSET_X) // SQUARE
    dr = (py - BOARD_OFFSET_Y) // SQUARE
    if not (0 <= dr < 8 and 0 <= dc < 8):
        return None
    c = 7 - dc if flipped else dc
    r = 7 - dr if flipped else dr
    return r, c


def draw_board(screen, gs, selected, highlights, font_piece, font_small, flipped=False):
    """Render squares, highlights, pieces, border, and coordinate labels.
    When flipped=True the board is shown from Black's perspective."""
    king_in_check = None
    if gs.status in ('check', 'checkmate'):
        king_in_check = king_pos(gs.board, gs.turn)

    for r in range(8):
        for c in range(8):
            light  = (r + c) % 2 == 0
            colour = C_LIGHT if light else C_DARK
            x, y   = sq_to_pixel(r, c, flipped)
            pygame.draw.rect(screen, colour, (x, y, SQUARE, SQUARE))

            # King-in-check red glow
            if king_in_check and (r, c) == king_in_check:
                s = pygame.Surface((SQUARE, SQUARE), pygame.SRCALPHA)
                s.fill(C_CHECK)
                screen.blit(s, (x, y))

            # Selected-piece green highlight
            if selected and (r, c) == selected:
                s = pygame.Surface((SQUARE, SQUARE), pygame.SRCALPHA)
                s.fill(C_SELECT)
                screen.blit(s, (x, y))

            # Legal-move hints — dot for empty, ring for capture
            if (r, c) in highlights:
                piece = gs.board[r][c]
                s = pygame.Surface((SQUARE, SQUARE), pygame.SRCALPHA)
                if piece is None or gs.ep_square == (r, c):
                    pygame.draw.circle(s, C_MOVE, (SQUARE//2, SQUARE//2), SQUARE//6)
                else:
                    pygame.draw.circle(s, C_MOVE, (SQUARE//2, SQUARE//2), SQUARE//2 - 3, 5)
                screen.blit(s, (x, y))

    # Pieces
    for r in range(8):
        for c in range(8):
            p = gs.board[r][c]
            if p:
                x, y  = sq_to_pixel(r, c, flipped)
                symbol = UNICODE[p]
                col_p  = (255, 255, 255) if p[0] == WHITE else (15, 15, 15)
                shadow = (50,  50,  50)  if p[0] == WHITE else (200, 200, 200)
                surf   = font_piece.render(symbol, True, shadow)
                screen.blit(surf, surf.get_rect(center=(x + SQUARE//2 + 2, y + SQUARE//2 + 2)))
                surf   = font_piece.render(symbol, True, col_p)
                screen.blit(surf, surf.get_rect(center=(x + SQUARE//2, y + SQUARE//2)))

    # Board border
    pygame.draw.rect(screen, (80, 60, 40),
                     (BOARD_OFFSET_X - 2, BOARD_OFFSET_Y - 2,
                      BOARD_SIZE + 4, BOARD_SIZE + 4), 3)

    # Coordinate labels — flip-aware
    files = 'abcdefgh' if not flipped else 'hgfedcba'
    for i in range(8):
        # File label at bottom-right of each column
        lbl = font_small.render(files[i], True, (160, 140, 120))
        screen.blit(lbl, (BOARD_OFFSET_X + i * SQUARE + SQUARE - 12,
                          BOARD_OFFSET_Y + BOARD_SIZE - 14))
        # Rank label at top-left of each row
        rank_num = str(i + 1) if flipped else str(8 - i)
        lbl = font_small.render(rank_num, True, (160, 140, 120))
        screen.blit(lbl, (BOARD_OFFSET_X + 3, BOARD_OFFSET_Y + i * SQUARE + 3))

    # Orientation indicator (tiny badge in top-right corner of board)
    badge_txt  = '▲ Black' if flipped else '▲ White'
    badge_col  = (180, 200, 255)
    badge_surf = font_small.render(badge_txt, True, badge_col)
    bx = BOARD_OFFSET_X + BOARD_SIZE - badge_surf.get_width() - 4
    by = BOARD_OFFSET_Y + 2
    screen.blit(badge_surf, (bx, by))


def draw_panel(screen, gs, font_ui, font_small,
               btn_new_rect, btn_new_hover,
               btn_flip_rect, btn_flip_hover, flipped):
    """Render the status bar and control buttons below the board."""
    pygame.draw.rect(screen, C_PANEL, (0, BOARD_OFFSET_Y + BOARD_SIZE, WIDTH,
                                       HEIGHT - BOARD_OFFSET_Y - BOARD_SIZE))

    # Turn / status text
    if gs.status == 'playing':
        name = "White's Turn" if gs.turn == WHITE else "Black's Turn"
        col  = (240, 230, 200)
    elif gs.status == 'check':
        name = "White is in CHECK!" if gs.turn == WHITE else "Black is in CHECK!"
        col  = (255, 120, 80)
    elif gs.status == 'checkmate':
        winner = "White" if gs.winner == WHITE else "Black"
        name   = f"CHECKMATE — {winner} wins!"
        col    = (100, 255, 140)
    else:
        name = "STALEMATE — Draw!"
        col  = (180, 180, 255)

    lbl = font_ui.render(name, True, col)
    screen.blit(lbl, lbl.get_rect(center=(WIDTH//2, BOARD_OFFSET_Y + BOARD_SIZE + 24)))

    # ── New Game button ──────────────────────
    bc = C_BTN_H if btn_new_hover else C_BTN
    pygame.draw.rect(screen, bc, btn_new_rect, border_radius=8)
    pygame.draw.rect(screen, (120, 160, 255), btn_new_rect, 2, border_radius=8)
    blbl = font_ui.render("New Game", True, (230, 235, 255))
    screen.blit(blbl, blbl.get_rect(center=btn_new_rect.center))

    # ── Flip Board button ────────────────────
    fc = C_BTN_H if btn_flip_hover else (50, 80, 130)
    pygame.draw.rect(screen, fc, btn_flip_rect, border_radius=8)
    pygame.draw.rect(screen, (100, 140, 220), btn_flip_rect, 2, border_radius=8)
    flip_label = "⟳ Flip Board"
    flbl = font_ui.render(flip_label, True, (210, 225, 255))
    screen.blit(flbl, flbl.get_rect(center=btn_flip_rect.center))


# Maps keyboard key → promotion kind (used during promotion overlay)
PROMO_KEY_MAP = {
    pygame.K_q: QUEEN,
    pygame.K_r: ROOK,
    pygame.K_b: BISHOP,
    pygame.K_n: KNIGHT,
}
PROMO_HOTKEYS = {QUEEN: 'Q', ROOK: 'R', BISHOP: 'B', KNIGHT: 'N'}


def build_promo_rects():
    """Return list of (pygame.Rect, kind) for the four promotion cards.
    Positions are fixed so they can be stored once and reused every frame."""
    total_w = len(PROMO_PIECES) * 120
    start_x = WIDTH // 2 - total_w // 2
    return [
        (pygame.Rect(start_x + i * 120, HEIGHT // 2 - 70, 108, 118), kind)
        for i, kind in enumerate(PROMO_PIECES)
    ]


def draw_promotion(screen, colour, promo_rects, font_piece, font_ui, font_small, mx, my):
    """Render the promotion choice overlay with hover highlight.
    promo_rects must be the list from build_promo_rects()."""
    # Dark semi-transparent backdrop
    overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    overlay.fill((8, 8, 18, 215))
    screen.blit(overlay, (0, 0))

    # Title
    who  = 'White' if colour == WHITE else 'Black'
    title = font_ui.render(f"{who}'s Pawn — Choose promotion:", True, (240, 225, 190))
    screen.blit(title, title.get_rect(center=(WIDTH // 2, HEIGHT // 2 - 100)))

    col_p = (255, 255, 255) if colour == WHITE else (15, 15, 15)

    for rect, kind in promo_rects:
        hovered = rect.collidepoint(mx, my)
        bg      = (80, 110, 180) if hovered else (40, 55, 95)
        border  = (160, 200, 255) if hovered else (90, 120, 190)

        # Card background with glow when hovered
        pygame.draw.rect(screen, bg, rect, border_radius=12)
        pygame.draw.rect(screen, border, rect, 2, border_radius=12)

        # Piece symbol
        sym  = UNICODE[(colour, kind)]
        ps   = font_piece.render(sym, True, col_p)
        screen.blit(ps, ps.get_rect(center=(rect.centerx, rect.top + 46)))

        # Piece name
        nl = font_ui.render(PROMO_LABELS[kind], True,
                            (220, 230, 255) if hovered else (160, 175, 210))
        screen.blit(nl, nl.get_rect(center=(rect.centerx, rect.bottom - 22)))

        # Keyboard shortcut hint
        hint = font_small.render(f'[{PROMO_HOTKEYS[kind]}]', True, (120, 150, 200))
        screen.blit(hint, hint.get_rect(center=(rect.centerx, rect.bottom - 6)))

    # Bottom instruction
    instr = font_small.render('Click a piece  or press  Q / R / B / N', True, (130, 140, 160))
    screen.blit(instr, instr.get_rect(center=(WIDTH // 2, HEIGHT // 2 + 80)))


# ─────────────────────────────────────────────
#  Main
# ─────────────────────────────────────────────
def main():
    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Chess")
    clock  = pygame.time.Clock()

    # Fonts — try a nice system font, fall back to default
    def load_font(size):
        for name in ('Segoe UI Symbol', 'Arial Unicode MS', 'DejaVu Sans',
                     'FreeSans', None):
            try:
                return pygame.font.SysFont(name, size)
            except Exception:
                pass
        return pygame.font.Font(None, size)

    font_piece = load_font(52)
    font_ui    = load_font(22)
    font_small = load_font(14)

    gs           = GameState()
    selected     = None          # (r, c) of selected square
    highlights   = set()         # set of (r, c) legal move targets
    promoting    = False         # waiting for promotion choice
    promo_pos    = None          # (tr, tc, fr, fc) pending promotion
    promo_colour = None
    promo_rects  = build_promo_rects()  # fixed rects, built once
    # flipped=True  → board shown from Black's perspective (row 0 at bottom)
    # auto_flip=True → board flips automatically after every move
    flipped      = False
    auto_flip    = True

    panel_y    = BOARD_OFFSET_Y + BOARD_SIZE
    btn_new_rect  = pygame.Rect(WIDTH//2 - 165, panel_y + 42, 150, 36)
    btn_flip_rect = pygame.Rect(WIDTH//2 +  15, panel_y + 42, 150, 36)

    running = True
    while running:
        clock.tick(FPS)
        mx, my        = pygame.mouse.get_pos()
        btn_new_hover  = btn_new_rect.collidepoint(mx, my)
        btn_flip_hover = btn_flip_rect.collidepoint(mx, my)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False

            # ── Keyboard shortcut for promotion (Q / R / B / N) ──────────
            elif event.type == pygame.KEYDOWN and promoting:
                chosen = PROMO_KEY_MAP.get(event.key)
                if chosen is not None:
                    tr, tc, fr, fc = promo_pos
                    do_move(gs, fr, fc, tr, tc, promote_to=chosen)
                    if auto_flip:
                        flipped = (gs.turn == BLACK)
                    promoting    = False
                    promo_pos    = None
                    promo_colour = None
                    selected     = None
                    highlights   = set()

            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                # ── New Game button ──────────────────────────────────
                if btn_new_rect.collidepoint(mx, my):
                    gs           = GameState()
                    selected     = None
                    highlights   = set()
                    promoting    = False
                    promo_pos    = None
                    promo_colour = None
                    flipped      = False   # reset to White-at-bottom
                    auto_flip    = True
                    continue

                # ── Flip Board button ────────────────────────────────
                if btn_flip_rect.collidepoint(mx, my):
                    flipped    = not flipped
                    auto_flip  = False     # manual flip → disable auto-flip
                    selected   = None
                    highlights = set()
                    continue

                # Promotion overlay — mouse click on a card
                if promoting:
                    chosen = None
                    for rect, kind in promo_rects:
                        if rect.collidepoint(mx, my):
                            chosen = kind
                            break
                    if chosen is not None:
                        tr, tc, fr, fc = promo_pos
                        do_move(gs, fr, fc, tr, tc, promote_to=chosen)
                        if auto_flip:
                            flipped = (gs.turn == BLACK)
                        promoting    = False
                        promo_pos    = None
                        promo_colour = None
                        selected     = None
                        highlights   = set()
                    continue

                if gs.status in ('checkmate', 'stalemate'):
                    continue

                sq = pixel_to_sq(mx, my, flipped)
                if sq is None:
                    selected   = None
                    highlights = set()
                    continue

                r, c = sq
                piece = gs.board[r][c]

                if selected is None:
                    # Select own piece
                    if piece and piece[0] == gs.turn:
                        selected   = (r, c)
                        highlights = set(legal_moves(gs, r, c))
                else:
                    # Attempt move
                    if (r, c) in highlights:
                        fr, fc   = selected
                        mv_piece = gs.board[fr][fc]
                        colour_m = mv_piece[0]
                        kind_m   = mv_piece[1]
                        back     = 7 if colour_m == WHITE else 0

                        if kind_m == PAWN and r == back:
                            # Defer promotion
                            promoting    = True
                            promo_pos    = (r, c, fr, fc)
                            promo_colour = colour_m
                            selected     = None
                            highlights   = set()
                        else:
                            do_move(gs, fr, fc, r, c)
                            # Auto-flip: show the board from the next player's POV
                            if auto_flip:
                                flipped = (gs.turn == BLACK)
                            selected   = None
                            highlights = set()
                    elif piece and piece[0] == gs.turn:
                        # Re-select different own piece
                        selected   = (r, c)
                        highlights = set(legal_moves(gs, r, c))
                    else:
                        selected   = None
                        highlights = set()

        # ── Draw ──────────────────────────────
        screen.fill(C_BG)
        draw_board(screen, gs, selected, highlights, font_piece, font_small, flipped)
        draw_panel(screen, gs, font_ui, font_small,
                   btn_new_rect, btn_new_hover,
                   btn_flip_rect, btn_flip_hover, flipped)

        if promoting:
            draw_promotion(screen, promo_colour, promo_rects,
                           font_piece, font_ui, font_small, mx, my)

        pygame.display.flip()

    pygame.quit()
    sys.exit()


if __name__ == '__main__':
    main()
