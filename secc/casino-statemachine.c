#include "secc.h"

// Casino Specification and Verification Challenge
// https://verifythis.github.io/casino/
// (C) 2022 Gidon Ernst

// This file presents two models of the Casino that just replicate the state machine.

enum state {
  STATE_IDLE,
  STATE_AVAILABLE,
  STATE_PLACED
};

enum action {
  ADD_TO_POT,
  REMOVE_FROM_POT,
  CREATE_GAME,
  PLACE_BET,
  DECIDE_BET
};

bool nondet_bool();
  _(ensures result :: low)
int nondet_int();
  _(ensures result :: low)


// The first, simple_game_specification, just executes the state transitions in a loop.,
// but is imprecise in the order of events depending on the corrent state.
void simple_game_specification()
  _(trace (add_to_pot | remove_from_pot | create_game | place_bet | decide_bet)*)
{
  enum state state = STATE_IDLE;

  while(nondet_bool())
    _(invariant state :: low)
    _(trace (add_to_pot | remove_from_pot | create_game | place_bet | decide_bet)*)
  {
    enum action action = nondet_int();

    if(action == ADD_TO_POT) {
      _(emit add_to_pot)
    }
    
    else if(action == REMOVE_FROM_POT && (state == STATE_IDLE || state == STATE_AVAILABLE)) {
      _(emit remove_from_pot)
    }
    
    else if(action == CREATE_GAME && state == STATE_IDLE) {
        state = STATE_AVAILABLE;
      _(emit create_game)
    }
    
    else if(action == PLACE_BET && state == STATE_AVAILABLE) {
        state = STATE_PLACED;
      _(emit place_bet)
    }
    
    else if(action == DECIDE_BET && state == STATE_PLACED) {
        state = STATE_IDLE;
      _(emit decide_bet)
    }
  }
}

// the second specification actually works right
void strong_game_specification()
  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
     (add_to_pot | remove_from_pot)*)
{
  enum state state = STATE_IDLE;

  while(nondet_bool() || state != STATE_IDLE)
    _(invariant state :: low)
    _(invariant state == STATE_IDLE || state == STATE_AVAILABLE || state == STATE_PLACED)
  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
     (add_to_pot | remove_from_pot)*
      if state == STATE_IDLE)

  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
    (add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* 
      if state == STATE_AVAILABLE)
  
  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
     (add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot*
      if state == STATE_PLACED)
  {
    enum action action = nondet_int();

    if(action == ADD_TO_POT) {
      _(emit add_to_pot)
    }
    
    else if(action == REMOVE_FROM_POT && (state == STATE_IDLE || state == STATE_AVAILABLE)) {
      _(emit remove_from_pot)
    }
    
    else if(action == CREATE_GAME && state == STATE_IDLE) {
        state = STATE_AVAILABLE;
      _(emit create_game)
    }
    
    else if(action == PLACE_BET && state == STATE_AVAILABLE) {
        state = STATE_PLACED;
      _(emit place_bet)
    }
    
    else if(action == DECIDE_BET && state == STATE_PLACED) {
        state = STATE_IDLE;
      _(emit decide_bet)
    }
  }
}

// The third discerns the different states by recursive functions, one for each state.
// Therefore, it becomes possible to precisely specify the respective trace to be produced,
// and keep the calling context at the same time (which has the prefix at that point).

void game_idle()
  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
     (add_to_pot | remove_from_pot)*)
{
  enum action action = nondet_int();

  if(action == ADD_TO_POT) {
    _(emit add_to_pot)
    game_idle();
  } else if(action == REMOVE_FROM_POT) {
    _(emit remove_from_pot)
    game_idle();
  } else if(action == CREATE_GAME) {
    _(emit create_game)
    game_available();
  } else {
    game_idle();
  }
}

void game_available()
  _(trace
    ((add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
    (add_to_pot | remove_from_pot)*)
{
  enum action action = nondet_int();

  if(action == ADD_TO_POT) {
    _(emit add_to_pot)
    game_available();
  } else if(action == REMOVE_FROM_POT) {
    _(emit remove_from_pot)
    game_available();
  } else if(action == PLACE_BET) {
    _(emit place_bet)
    game_placed();
  } else {
    game_available();
  }
}

void game_placed()
  _(trace
     (add_to_pot* decide_bet)
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* decide_bet)*
    (add_to_pot | remove_from_pot)*)
{
  enum action action = nondet_int();

  if(action == ADD_TO_POT) {
    _(emit add_to_pot)
    game_placed();
  } else if(action == DECIDE_BET) {
    _(emit decide_bet)
    game_idle();
  } else {
    game_placed();
  }
}
