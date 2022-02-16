package game;

import static game.Mark.*;

/**
 * @author DavidHurst
 */
public class Board {

    private /*@ spec_public @*/ final Mark[][] board;
    private /*@ spec_public @*/ Mark winningMark;
    private /*@ spec_public @*/ final int BOARD_WIDTH = 3;
    private /*@ spec_public @*/ boolean crossTurn, gameOver;
    private /*@ spec_public @*/ int availableMoves = BOARD_WIDTH * BOARD_WIDTH;

    /*@ requires 0 < BOARD_WIDTH;
    @ assignable board, crossTurn, gameOver, winningMark, availableMoves, BOARD_WIDTH;
    @ ensures board.length == BOARD_WIDTH;
    @ ensures board[0].length == BOARD_WIDTH;
    @ ensures availableMoves == (BOARD_WIDTH * BOARD_WIDTH);
    @ ensures crossTurn == true;
    @ ensures gameOver == false;
    @ ensures winningMark == BLANK;
    @*/
    public Board() {
        board = new Mark[BOARD_WIDTH][BOARD_WIDTH];
        crossTurn = true;
        gameOver = false;
        winningMark = BLANK;
        initialiseBoard();
    }

    /*@ requires 0 < BOARD_WIDTH;
    @ assignable board;
    @ ensures (\forall int i, j;
    @       0 <= i && i < BOARD_WIDTH && 0 <= j && i < BOARD_WIDTH;
    @       elems[i][j] == BLANK);
    @*/
    private void initialiseBoard() {
        for (int row = 0; row < BOARD_WIDTH; row++) {
            for (int col = 0; col < BOARD_WIDTH; col++) {
                board[row][col] = BLANK;
            }
        }
    }

    /**
     * Attempt to mark tile at the given coordinates if they are valid and it is
     * possible to do so, toggle the player and check if the placing the mark
     * has resulted in a win.
     *
     * @param row Row coordinate to attempt to mark
     * @param col Column coordinate to attempt to mark
     * @return true if mark was placed successfully
     */
    /*@ requires 0 <= row;
    @ requires 0 <= column;
    @ {|
    @   requires row < 0 || row >= BOARD_WIDTH || col < 0 || col >= BOARD_WIDTH || isTileMarked(row, col) || gameOver;
    @   ensures \result == false;
    @ also
    @   requires !(row < 0 || row >= BOARD_WIDTH || col < 0 || col >= BOARD_WIDTH || isTileMarked(row, col) || gameOver) == false;
    @   assignable availableMoves, board[row][col];
    @   ensures availableMoves == \old(availableMoves - 1);
    @   ensures board[row][col] = crossTurn ? X : O;
    @   ensures \result == true;
    @ |}
    @*/
    public boolean placeMark(int row, int col) {
        if (row < 0 || row >= BOARD_WIDTH || col < 0 || col >= BOARD_WIDTH
                || isTileMarked(row, col) || gameOver) {
            return false;
        }
        availableMoves--;
        board[row][col] = crossTurn ? X : O;
        togglePlayer();
        checkWin(row, col);
        return true;
    }

    /**
     * Check row and column provided and diagonals for win.
     *
     * @param row Row to check
     * @param col Column to check
     */
    private void checkWin(int row, int col) {
        int rowSum = 0;
        // Check row for winner.
        for (int c = 0; c < BOARD_WIDTH; c++) {
            rowSum += getMarkAt(row, c).getMark();
        }
        if (calcWinner(rowSum) != BLANK) {
            System.out.println(winningMark + " wins on row " + row);
            return;
        }

        // Check column for winner.
        rowSum = 0;
        for (int r = 0; r < BOARD_WIDTH; r++) {
            rowSum += getMarkAt(r, col).getMark();
        }
        if (calcWinner(rowSum) != BLANK) {
            System.out.println(winningMark + " wins on column " + col);
            return;
        }

        // Top-left to bottom-right diagonal.
        rowSum = 0;
        for (int i = 0; i < BOARD_WIDTH; i++) {
            rowSum += getMarkAt(i, i).getMark();
        }
        if (calcWinner(rowSum) != BLANK) {
            System.out.println(winningMark + " wins on the top-left to "
                    + "bottom-right diagonal");
            return;
        }

        // Top-right to bottom-left diagonal.
        rowSum = 0;
        int indexMax = BOARD_WIDTH - 1;
        for (int i = 0; i <= indexMax; i++) {
            rowSum += getMarkAt(i, indexMax - i).getMark();
        }
        if (calcWinner(rowSum) != BLANK) {
            System.out.println(winningMark + " wins on the top-right to "
                    + "bottom-left diagonal.");
            return;
        }

        if (!anyMovesAvailable()) {
            gameOver = true;
            System.out.println("Tie!");
        }
    }

    /**
     * Calculates if provided ASCII sum equates to a win for X or O.
     *
     * @param rowSum Sum of characters' ASCII values in a row
     * @return Mark indicating which player won or a space character if neither
     */
    /*@ requires 0 <= rowSum;
    @ {|
    @   requires rowSum == (X.getMark() * BOARD_WIDTH);
    @   assignable gameover, winningMark;
    @   ensures gameOver == true;
    @   ensures winningMark == X;
    @   ensures \result == X;
    @ also
    @   requires rowSum == (O.getMark() * BOARD_WIDTH);
    @   assignable gameover, winningMark;
    @   ensures gameOver == true;
    @   ensures winningMark == O;
    @   ensures \result == O;
    @ also
    @   requires rowSum != (O.getMark() * BOARD_WIDTH) && rowSum != (X.getMark() * BOARD_WIDTH);
    @   ensures \result == BLANK;
    @ |}
    @*/
    private Mark calcWinner(int rowSum) {
        int Xwin = X.getMark() * BOARD_WIDTH;
        int Owin = O.getMark() * BOARD_WIDTH;
        if (rowSum == Xwin) {
            gameOver = true;
            winningMark = X;
            return X;
        } else if (rowSum == Owin) {
            gameOver = true;
            winningMark = O;
            return O;
        }
        return BLANK;
    }

    /*@ assignable crossTurn;
    @ ensures crossTurn == \old(!crossTurn);
    @*/
    private void togglePlayer() {
        crossTurn = !crossTurn;
    }

    /*@ assignable \nothing;
    @ ensures \result == (availableMoves > 0);
    @*/
    @SuppressWarnings("BooleanMethodIsAlwaysInverted")
    public /*@ pure @*/ boolean anyMovesAvailable() {
        return availableMoves > 0;
    }

    /*@ requires 0 <= row;
    @ requires 0 <= column;
    @ assignable \nothing;
    @ ensures \result == board[row][column];
    @*/
    public /*@ pure @*/ Mark getMarkAt(int row, int column) {
        return board[row][column];
    }

    /*@ requires 0 <= row;
    @ requires 0 <= column;
    @ assignable \nothing;
    @ ensures \result == board[row][column].isMarked();
    @*/
    public /*@ pure @*/ boolean isTileMarked(int row, int column) {
        return board[row][column].isMarked();
    }

    /*@ requires 0 <= row;
    @ requires 0 <= column;
    @ assignable board[row][column];
    @ ensures board[row][column] == newMark;
    @*/
    public void setMarkAt(int row, int column, /*@ non_null @*/ Mark newMark) {
        board[row][column] = newMark;
    }

    @Override
    public String toString() {
        StringBuilder strBldr = new StringBuilder();
        for (Mark[] row : board) {
            for (Mark tile : row) {
                strBldr.append(tile).append(' ');
            }
            strBldr.append("\n");
        }
        return strBldr.toString();
    }

    /*@ assignable \nothing;
    @ ensures \result == crossTurn;
    @*/
    public /*@ pure @*/ boolean isCrossTurn() {
        return crossTurn;
    }

    /*@ assignable \nothing;
    @ ensures \result == BOARD_WIDTH;
    @*/
    public /*@ pure @*/ int getWidth() {
        return BOARD_WIDTH;
    }

    /*@ assignable \nothing;
    @ ensures \result == gameOver;
    @*/
    public /*@ pure @*/ boolean isGameOver() {
        return gameOver;
    }

    /*@ assignable \nothing;
    @ ensures \result == winningMark;
    @*/
    public /*@ pure @*/ Mark getWinningMark() {
        return winningMark;
    }
}
