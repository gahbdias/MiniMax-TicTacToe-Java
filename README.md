# MiniMax Tic Tac Toe



## Tic Tac Toe

The Tic Tac Toe GUI is implemented using JavaFX, the board size is variable and can be altered by changing the BOARD_WIDTH constant in the Board class. Boards of size 4x4 or larger with a maximum search depth over 6 are essentially unplayable using the vanilla MiniMax algorithm but the Alpha-Beta optimisation improves this dramatically allowing for much larger games to be played and the MiniMaxImproved implementation improves the heuristic used to evaluate boards making the algorithm win faster or lose slower. MiniMaxCombined combines the improved heuristic with alpha-beta optimisation.

 ![3x3Board](https://github.com/DavidHurst/MiniMax-TicTacToe-Java/blob/master/Images/3x3Board.PNG "3x3Board"){:height="400px" width="300px"}  ![4x4Board](https://github.com/DavidHurst/MiniMax-TicTacToe-Java/blob/master/Images/4x4Board.PNG "4x4Board"){:height="400px" width="300px"}  ![5x5Board](https://github.com/DavidHurst/MiniMax-TicTacToe-Java/blob/master/Images/5x5Board.PNG "5x5Board"){:height="400px" width="300px"}



## MiniMax

The Minimax algorithm uses backtracking to recursively find the next best move by assigning a value to each board configuration and evaluating each of these configurations using a heuristic evaluation function. In the vanilla implementation of MiniMax ([MiniMax.java](http://minimax.java)) the evaluation function returns a heuristic value for terminal nodes and nodes at the predetermined maximum search depth but the heuristic only takes into account winning, losing and draw configurations returning +10 for winning configurations, -10 for losing and 0 for a draw which slightly hinders the performance of the algorithm in terms of time to win, this is addressed in MiniMaxImproved. 

This implementation also explores every possible board configuration it can, even when it is redundant to do so resulting in a time complexity of O(b^d) where *b* is how many legal moves there are from a board configuration (i.e. the branching factor of the game tree) and *d* is the maximum depth of the tree, this inefficiency is addressed with the Alpha-Beta optimisation.



## MiniMax Improved

The vanilla MiniMax algorithm's heuristic function sometimes results in a slower victory or a faster loss due to the heuristic not taking into account the depth of the winning configuration. MiniMaxImproved and MiniMaxCombined address this by adding the depth to maximising evaluations and takning depth away from minimising evaluations, this has the effect of making wins which can be achieved in fewer moves more favourable and loses which can be achieved in the most moves more favourable.

 ![SlowVictory](https://github.com/DavidHurst/MiniMax-TicTacToe-Java/blob/master/Images/SlowVictory.gif "SlowVictory"){:height="400px" width="300px"} ![FastVictory](https://github.com/DavidHurst/MiniMax-TicTacToe-Java/blob/master/Images/FastVictory.gif "FastVictory"){:height="400px" width="300px"}



## Alpha-Beta Pruning

Alpha-Beta pruning optimises the Minimax algorithm by not evaluating a node's children when at least one possibility has been found that proves the node to be worse than a previously examined move, this is known as pruning.

- Alpha is associated with the *max* nodes and represents the minimum score that the maximising player is assured of i.e. the best alternative for the maximising player.
- Beta is associated with *min* nodes and represents the maximum score that the minimising player is assured of i.e. the best alternative for the minimising player.

Pruning when it is the minimising player's turn can be done whenever alpha ≥ beta, this represents the node being worse for the maximising player than it's best alternative and therefore that the children of this node will never actually be reached in play. Similarly, the maximising player can prune whenever beta ≤ alpha, representing the node being worse for the minimising player than it's best alternative. 

Alpha-Beta improves MiniMax's efficiency from O(b^d) to O(sqrt(b^d)) because:
"all the first player's moves must be studied to find the best one, but for each, only the second player's best move is needed to refute all but the first (and best) first player move—alpha–beta ensures no other second player moves need be considered." - Wikipedia.

---

### Resources
[Minimax with Alpha Beta Pruning - John Levine](https://www.youtube.com/watch?v=zp3VMe0Jpf8)

[Search: Games, Minimax, and Alpha-Beta - MIT OpenCourseWare](https://www.youtube.com/watch?v=STjW3eH0Cik)

[Alpha-Beta Pruning - Wikipedia](https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning)

[Minimax - Wikipedia](https://en.wikipedia.org/wiki/Minimax)

[What is the Minimax Algorithm? - Gaurav Sen](https://www.youtube.com/watch?v=KU9Ch59-4vw)

[MiniMax and Alpha-Beta Pruning - Sebastian Lague](https://www.youtube.com/watch?v=l-hh51ncgDI)

[Coding Challenge 154: Tic Tac Toe AI with Minimax Algorithm - The Coding Train](https://www.youtube.com/watch?v=trKjYdBASyQ)

[Minimax Algorithm in Game Theory - Geeks for Geeks](https://www.geeksforgeeks.org/minimax-algorithm-in-game-theory-set-3-tic-tac-toe-ai-finding-optimal-move/?ref=lbp)
