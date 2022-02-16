
package game;

/**
 * @author <a href="mailto:peter.vakulin@protonmail.com">Peter Vakulin</a>
 */

public enum Mark {
    X('X'),
    O('O'),
    BLANK(' ');

    private final char mark;
    
    Mark(char initMark) {
        this.mark = initMark;
    }
    
    /*@
    @ assignable \nothing;
    @ ensures \result == true || \result == false;
    @*/
    public /*@ pure @*/ boolean isMarked() {
        return this != BLANK;
    }
    
    /*@
    @ assignable \nothing;
    @ ensures \result == 'X' || \result == 'O' || \result == ' ';
    @*/
    public /*@ pure @*/ char getMark() {
        return this.mark;
    }
    
    /*@
    @ assignable \nothing;
    @ ensures \result == 'X' || \result == 'O' || \result == ' ';
    @*/
    @Override
    public /*@ pure @*/ String toString() {
        return String.valueOf(mark);
    }
}
