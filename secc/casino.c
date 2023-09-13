#include "secc.h"

// Casino Specification and Verification Challenge
// https://verifythis.github.io/casino/
// (C) 2022 Gidon Ernst

// Model of a cryptographic hash function together with a logical specification
_(function int _cryptohash(int x))
int cryptohash(int x);
  _(ensures result == _cryptohash(x))

// Abstract type of addresses on the blockchain
struct address;

// Abstract predicate that encodes ownership of an account
_(predicate
  account(struct address *address; int balance))

// Abstract predicate that reflects a payment that has not yet been cashed in
_(predicate
  payment(struct address *sender, struct address *receiver;  int amount))

// The two predicates are connected by this specification function,
// which is to be called in the beginning of a payable method.
// This is technically enforced by otherwise leaking the payable heap chunk
// (which causes a verification error)
void receive(struct address *self, struct address *sender);
  _(requires payment(sender, self; ?amount))
  _(requires account(self; ?balance))
  _(ensures  account(self; balance + amount) && amount >= 0)

// Alternatively, we can ignore the payment entirely
void receive_later(struct address *self, struct address *sender);
  _(requires payment(sender, self; ?amount))
  
// Abstract method to transfer money.
// It models only the side of the sender, the money just disappears :)
// The return value indicates whether the transfer was successful,
// if not, this method ensures false to reflect the aborted/nonterminating execution.
// Note, this does not actually affect the verification in any way.
bool transfer(struct address *self, struct address *receiver, int amount);
  _(requires account(self; ?balance) && balance >= amount)
  _(ensures  result :: low)
  _(ensures  result ? account(self; balance - amount) && payment(self, receiver; amount) : false) // model aborted call here

enum state {
  STATE_UNKNOWN,
  STATE_IDLE,
  STATE_AVAILABLE,
  STATE_PLACED
};

enum coin {
  HEADS, TAILS
};

// State of the Casino itself, the address of the Casino contract is not represented here.
struct casino {
  enum state state;

  struct address *operator;
  int hash;

  struct address *player;
  enum coin guess;

  int  pot;
  int  bet;
};

// Predicate that gives ownership to the C structure, with all fields modeled
// as publicly observable (low) locations, as they are stored in the blockchain.
// We keep track of the invariant that there is sufficient balance int the account to handle remove_from_pot and decide_bet.
_(predicate
  game(
      struct address *self,
      struct casino *casino;
      int _balance,
      enum state _state,
      struct address *_operator, int _hash,
      struct address *_player, enum coin _guess,
      int _pot, int _bet)
  account(self; _balance) && 0 <= _balance

  && &casino->state    |->[low] _state
  && &casino->operator |->[low] _operator
  && &casino->hash     |->[low] _hash
  && &casino->player   |->[low] _player
  && &casino->guess    |->[low] _guess
  && &casino->pot      |->[low] _pot
  && &casino->bet      |->[low] _bet

  && (bool)(_state == STATE_IDLE || _state == STATE_AVAILABLE
        ==> _pot <= _balance)

  // this one is actually not needed:
  // && (bool)(_state == STATE_AVAILABLE || _state == STATE_PLACED
  //      ==> exists int secret. _hash == _cryptohash(secret))

  && (bool)(_state == STATE_PLACED
        ==> _player != null && _bet <= _pot && _pot + _bet <= _balance))

void init(struct address *self, struct address *sender, struct casino *casino)
  _(requires self :: low && sender :: low && casino :: low)
  _(requires game(self, casino; ?_balance, STATE_UNKNOWN, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(ensures  game(self, casino;  _balance, STATE_IDLE,     sender,     _hash,  null,     _guess, 0, 0))
  _(trace init)
{
  _(unfold game(self, casino; _balance, STATE_UNKNOWN, _operator, _hash, _player, _guess, _pot, _bet))

  casino->state = STATE_IDLE;
  casino->operator = sender;
  casino->player = NULL;
  casino->pot = 0;
  casino->bet = 0;

  _(emit init)
  _(fold game(self, casino; _balance, STATE_IDLE, sender, _hash, null, _guess, 0, 0))
}

void add_to_pot(struct address *self, struct address *sender, int amount, struct casino *casino)
  _(requires self :: low && sender :: low && amount :: low && casino :: low)
  _(requires payment(sender, self; amount))
  _(requires game(self, casino; ?_balance, ?_state, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(requires sender == _operator && 0 <= amount)
  _(ensures  game(self, casino; _balance + amount, _state, _operator, _hash, _player, _guess, _pot + amount, _bet))
  _(trace add_to_pot)
{
  _(unfold game(self, casino; _balance, _state, _operator, _hash, _player, _guess, _pot, _bet))
  receive(self, sender);
  casino->pot += amount;
  _(emit add_to_pot)
  _(fold   game(self, casino; _balance + amount, _state, _operator, _hash, _player, _guess, _pot + amount, _bet))
}

void remove_from_pot(struct address *self, struct address *sender, struct casino *casino, int amount)
  _(requires self :: low && sender :: low && casino :: low && amount :: low)
  _(requires game(self, casino; ?_balance, ?_state, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(requires sender == _operator && 0 <= amount && amount <= _pot)
  _(requires _state == STATE_IDLE || _state == STATE_AVAILABLE)
  _(ensures  game(self, casino; _balance - amount, _state, _operator, _hash, _player, _guess, _pot - amount, _bet))
  _(ensures  payment(self, sender; amount))
  _(trace remove_from_pot)
{
  _(unfold game(self, casino; _balance, _state, _operator, _hash, _player, _guess, _pot, _bet))
  transfer(self, sender, amount);
  casino->pot -= amount;
  _(emit remove_from_pot)
  _(fold   game(self, casino; _balance - amount, _state, _operator, _hash, _player, _guess, _pot - amount, _bet))
}

void create_game(struct address *self, struct address *sender, struct casino *casino, int hash)
  _(requires self :: low && sender :: low && casino :: low && hash :: low)
  _(requires game(self, casino; ?_balance, STATE_IDLE, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(requires sender == _operator)
  // _(requires exists int secret. hash == _cryptohash(secret))
  _(ensures  game(self, casino; _balance, STATE_AVAILABLE, _operator, hash, _player, _guess, _pot, _bet))
  _(trace create_game)
{
  _(unfold game(self, casino; _balance, STATE_IDLE, _operator, _hash, _player, _guess, _pot, _bet))
  casino->state = STATE_AVAILABLE;
  casino->hash  = hash;
  _(emit create_game)
  _(fold game(self, casino; _balance, STATE_AVAILABLE, _operator, hash, _player, _guess, _pot, _bet))
}

void place_bet(struct address *self, struct address *sender, int amount, struct casino *casino, enum coin guess)
  _(requires self :: low && sender :: low && amount :: low && casino :: low && guess :: low)
  _(requires payment(sender, self; amount))
  _(requires game(self, casino; ?_balance, STATE_AVAILABLE, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(requires sender != null && sender != _operator && amount <= _pot)
  _(ensures  game(self, casino; _balance + amount, STATE_PLACED, _operator, _hash, sender, guess, _pot, amount))
  _(trace place_bet)
{
  _(unfold game(self, casino; _balance, STATE_AVAILABLE, _operator, _hash, _player, _guess, _pot, _bet))
  receive(self, sender);
  casino->state  = STATE_PLACED;
  casino->player = sender;
  casino->guess  = guess;
  casino->bet    = amount;
  _(emit place_bet)
  _(fold game(self, casino; _balance + amount, STATE_PLACED, _operator, _hash, sender, guess, _pot, amount))
}

int decide_bet(struct address *self, struct address *sender, struct casino *casino, int secret)
  _(requires self :: low && sender :: low && casino :: low && (secret % 2) :: low)
  _(requires game(self, casino; ?_balance, STATE_PLACED, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(requires // Here we require that the caller knows the secret from the creation of the auction
    sender == _operator && _hash == _cryptohash(secret))
  _(ensures result :: low)
  _(ensures result ==> payment(self, _player; 2*_bet))
  _(ensures game(self, casino; result ? _balance - 2*_bet : _balance, STATE_IDLE, _operator, _hash, _player, _guess, result ? _pot - _bet : _pot + _bet, 0))
  _(trace player_wins if result)
  _(trace casino_wins if !result) /* TODO: causes a bug in sequential game */
{
  enum coin coin = (secret % 2 ? HEADS : TAILS);
  _(unfold game(self, casino; _balance, STATE_PLACED, _operator, _hash, _player, _guess, _pot, _bet))

  // Note: Here it is crucial that the test whether
  //    casino->guess == secret % 2 ? HEADS : TAILS
  // is public, which follows of course from the precondition
  // that the secret has already been released to the public (by the operator).
  if(casino->guess == coin) {
    int prize = 2*casino->bet;
    struct player *winner = casino->player;
    transfer(self, winner, prize);
    casino->state = STATE_IDLE;
    casino->pot -= casino->bet;
    casino->bet  = 0;
    _(emit player_wins)
    _(fold game(self, casino; _balance - 2*_bet, STATE_IDLE, _operator, _hash, _player, _guess, _pot - _bet, 0))
    return 1;
  } else {
    casino->state = STATE_IDLE;
    casino->pot += casino->bet;
    casino->bet  = 0;
    _(emit casino_wins)
    _(fold game(self, casino; _balance, STATE_IDLE, _operator, _hash, _player, _guess, _pot + _bet, 0))
    return 0;
  }
}

bool nondet_bool();
  _(ensures result :: low)
int nondet_int();
  _(ensures result :: low)
int nondet_int_secret();
  _(ensures result :: high)

enum action {
  ADD_TO_POT,
  REMOVE_FROM_POT,
  CREATE_GAME,
  PLACE_BET,
  DECIDE_BET
};

// Run the game as a sequential nondeterministic sequence of actions.
// This allows us to specify the overall behavior as a single regular expression,
// whereas if the game runs in two (or more) threads, we do not yet have a way to interleave them properly
// (which seems to be a data-dependen property because of blocked actions).
// Moreover, we can prove something about when the operator decides to declassify the secret.
void sequential_game(struct address *self, struct address *operator, struct address *player, struct casino *casino, int operator_balance, int player_balance)
  _(requires self :: low && operator :: low && player :: low && casino :: low)
  _(requires
     account(self; ?_balance) && _balance >= 0)
  _(requires
     account(operator; operator_balance) && operator_balance >= 0 && operator_balance :: low)
  _(requires
     account(player; ?player_balance) && player_balance >= 0 && player_balance :: low)
  _(requires
    operator != null && player != null && player != operator)
  
  _(requires exists
      enum state _state,
      struct address *_operator, int _hash,
      struct address *_player, enum coin _guess,
      int _pot, int _bet.
         &casino->state    |->[low] _state
      && &casino->operator |->[low] _operator
      && &casino->hash     |->[low] _hash
      && &casino->player   |->[low] _player
      && &casino->guess    |->[low] _guess
      && &casino->pot      |->[low] _pot
      && &casino->bet      |->[low] _bet)
  _(ensures game(self, casino; ?_balance, ?_state, ?_operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
  _(ensures account(operator; ?_operator_balance))
  _(ensures account(player; ?_player_balance))

  _(trace init
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* (player_wins | casino_wins))*
     (add_to_pot | remove_from_pot)*)
{
  casino->state = STATE_UNKNOWN;
  _(fold game(self, casino; _balance, STATE_UNKNOWN, _operator, _hash, _player, _guess, _pot, _bet))

  init(self, operator, casino);

  int secret;
  int state = STATE_IDLE;

  while(nondet_bool() || state != STATE_IDLE)

    _(invariant game(self, casino; ?_balance, state, operator, ?_hash, ?_player, ?_guess, ?_pot, ?_bet))
    _(invariant account(operator; operator_balance))
    _(invariant 0 <= operator_balance && operator_balance :: low)

    _(invariant account(player; player_balance))
    _(invariant 0 <= player_balance && player_balance :: low)

    _(invariant (bool)(state == STATE_AVAILABLE || state == STATE_PLACED
        ==> _hash == _cryptohash(secret)))
    _(invariant state :: low)
    _(invariant state == STATE_IDLE || state == STATE_AVAILABLE || state == STATE_PLACED)

    _(invariant state == STATE_PLACED
        ==> _player == player)

  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* (player_wins | casino_wins))*
     (add_to_pot | remove_from_pot)*
      if state == STATE_IDLE)

  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* (player_wins | casino_wins))*
    (add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* 
      if state == STATE_AVAILABLE)
  
  _(trace
    ((add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot* (player_wins | casino_wins))*
     (add_to_pot | remove_from_pot)* create_game
     (add_to_pot | remove_from_pot)* place_bet
      add_to_pot*
      if state == STATE_PLACED)
  {
    _(unfold game(self, casino; _balance, state, operator, _hash, _player, _guess, _pot, _bet))

    int  action            = nondet_int();
    // struct address *player = casino->player;
    int  pot               = casino->pot;

    _(fold   game(self, casino; _balance, state, operator, _hash, _player, _guess, _pot, _bet))

    if(action == ADD_TO_POT) {
      int amount = nondet_int();
      if(0 <= amount && amount <= operator_balance) {
        transfer(operator, self, amount);
        add_to_pot(self, operator, amount, casino);
        operator_balance -= amount;
      }
    }
    
    else if(action == REMOVE_FROM_POT && (state == STATE_IDLE || state == STATE_AVAILABLE)) {
      int amount = nondet_int();
      if(0 <= amount && amount <= pot) {
        remove_from_pot(self, operator, casino, amount);
        receive(operator, self);
        operator_balance += amount;
      }
    }
    
    else if(action == CREATE_GAME && state == STATE_IDLE) {
      secret = nondet_int();
      int hash = cryptohash(secret);
      create_game(self, operator, casino, hash);
      state = STATE_AVAILABLE;
    }
    
    else if(action == PLACE_BET && state == STATE_AVAILABLE) {
      // separate thread?
      int amount = nondet_int();
      if(0 <= amount && amount <= player_balance && amount <= pot) {
        int number = nondet_int();
        int guess = (number % 2 ? HEADS : TAILS);

        if(transfer(player, self, amount)) {
          place_bet(self, player, amount, casino, guess);
          player_balance -= amount;
          state = STATE_PLACED;
          _(assume 0)
        }
      }
    }
    
    else if(action == DECIDE_BET && state == STATE_PLACED) {
      // Here, the operator wants to decide the bet and alongside needs
      // to release the secret to the blockchain.
      // What if there is a race-condition?
      // How does the EVM guarantee that the transaction is completed
      // once the call with the secret is written to the blockchain?
      _(assume secret :: low)
      int player_wins = decide_bet(self, operator, casino, secret);
      if(player_wins) {
        receive_later(player, self);
      }
      state = STATE_IDLE;
    }
  }
}