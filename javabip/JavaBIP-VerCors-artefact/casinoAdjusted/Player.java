package org.javabip.spec.casinoAdjusted;

import org.javabip.annotations.*;
import org.javabip.api.PortType;
import static org.javabip.spec.casinoAdjusted.Constants.*;
import static org.javabip.spec.casinoAdjusted.Coin.*;

@Port(name = PREPARE_BET, type = PortType.enforceable)
@Port(name = PLACE_BET, type = PortType.enforceable)
@Port(name = RECEIVE_MONEY, type = PortType.enforceable)
@ComponentType(initial = GAME_AVAILABLE, name = PLAYER_SPEC)
@Invariant("purse >= 0")
@StatePredicate(state = BET_PREPARED, expr = "guess != null && bet >= 0")
public class Player {
    final int id;
    int bet;
    Coin guess;
    int purse;

    //@ requires purse >= 0;
    Player(int id, int purse) {
        this.id = id;
        this.purse = purse;
//        System.out.println("PLAYER" + id + ": created (purse=" + purse + ")");
    }
    
    // Player prepares a bet
    @Transition(name = PREPARE_BET, source = GAME_AVAILABLE, target = BET_PREPARED)
    public void prepareBet() {
            bet = (purse == 0) ? 0 : (int) (Math.random() * purse) + 1;
            guess = Math.random() < 0.5 ? HEADS : TAILS;
            purse = purse - bet;
//            System.out.println("PLAYER" + id + ": bet " + bet + " prepared, purse: " + purse);
    }

    // Player places a bet
    @Transition(name = PLACE_BET, source = BET_PREPARED, target = GAME_AVAILABLE)
    public void placeBet() {
//            System.out.println("PLAYER" + id + ": bet " + bet + " placed, purse: " + purse);
            bet = 0;
            guess = null;
    }

    // Player receives a contribution
    @Transition(name = RECEIVE_MONEY, source = GAME_AVAILABLE, target = GAME_AVAILABLE,
        requires = "win >= 0" // Needed, otherwise VerCors cannot prove invariant again. E.g. what if win is negative? This is excluded by the casino invariant "bet >= 0"
    )
    @Transition(name = RECEIVE_MONEY, source = BET_PREPARED, target = BET_PREPARED,
            requires = "win >= 0" // Needed, otherwise VerCors cannot prove invariant again. E.g. what if win is negative? This is excluded by the casino invariant "bet >= 0"
    )
    public void receiveContribution(@Data(name = INCOMING_MONEY) int win) {
            purse += win;
//            System.out.println("PLAYER" + id + ": won " + win + " purse: " + purse);
    }

    @Data(name = OUTGOING_BET)
    @Pure
    public int getBet() {
            return bet;
    }

    @Data(name = OUTGOING_GUESS)
    @Pure
    public Coin getGuess() {
            return guess;
    }

    @Data(name = ID)
    @Pure
    public int id() {
            return id;
    }
}
