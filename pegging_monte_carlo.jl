###########################################################
# LOAD MODULES
###########################################################
using Combinatorics
using Random
using CSV
using DataFrames
###########################################################
# DEFINE CONSTANTS
###########################################################
const combns2 = combinations(1:4,2)|>collect
const combns3 = combinations(1:4,3)|>collect
const full_hand = combinations(1:4,4)|>collect
const suit_names = ["♣", "♦", "♥", "♠"]
const rank_names = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
###########################################################
# SET UP STRUCTS
###########################################################
# define card struct
struct card
    suit :: Int64
    rank :: Int64
    value :: Int64
    function card(suit::Int64, rank::Int64, value::Int64)
        @assert(1 ≤ suit ≤ 4, "suit is not between 1 and 4")
        @assert(1 ≤ rank ≤ 13, "rank is not between 1 and 13")
        @assert(1 ≤ value ≤ 10, "value is not between 1 and 10")
        new(suit, rank, value)
    end
end
# define print method
function Base.show(io::IO, card::card)
    print(io, rank_names[card.rank], suit_names[card.suit])
end
#define deck struct
abstract type card_set end

struct deck <: card_set
    cards :: Array{card, 1}
end
function deck()
        Deck = deck(card[])
        for suit in 1:4
            for rank in 1:13
                if rank ≤ 10
                push!(Deck.cards, card(suit, rank, rank))
            else
                push!(Deck.cards, card(suit, rank, 10))
            end
            end
        end
        Deck
    end
end
function Base.show(io::IO, deck::deck)
    for card in deck.cards
        print(io, card, " ")
    end
    println()
end
struct hand <: card_set
    cards :: Array{card, 1}
    label :: String
end
function hand(label::String="")
    hand(card[], label)
end
function Base.show(io::IO, cs::card_set)
    for card in cs.cards
        print(io, card, " ")
    end
end
function Base.pop!(cs::card_set)
    pop!(cs.cards)
end
function Base.deleteat!(cs::card_set, i)
    deleteat!(cs.cards, i::Int64)
end
function Base.push!(cs::card_set, card::card)
    push!(cs.cards, card)
    nothing
end
function move!(cs1::card_set, cs2::card_set, n::Int)
    @assert 1 ≤ n ≤ length(cs1.cards)
    for i in 1:n
        card = pop!(cs1)
        push!(cs2, card)
    end
    nothing
end
function Random.shuffle!(deck::deck)
    shuffle!(deck.cards)
    deck
end
function Base.isless(c1::card, c2::card)
    c1.rank < c2.rank
end
###########################################################
# DEFINE FUNCTIONS
###########################################################
# score hand needs some work--a lot of the garbage collection overhead comes from this function
# what are the alternatives to creating storage vectors in every iteration?
# using temporary vectors is admittedly inelegant and the major speed bottleneck in the simulations (~50% of the random pegging time is GC overhead)
# they may be fast enough to answer the question but 30-50% gc time suggests I need an alternative...
function score_hand(hand_combn)
    hand_scores = Int[]
    for sel_hand in hand_combn
        fifteens = Int[]
        pairs = Int[]
        runs = Int[]
        flush = Int[]
        for combn in combns2
            # check 2 card combinations for 15s
            if sel_hand[combn[1]].value + sel_hand[combn[2]].value == 15
                push!(fifteens, 2::Int)
            end
            # check 2 card combinations for pairs
            if sel_hand[combn[1]].rank == sel_hand[combn[2]].rank
                push!(pairs, 2::Int)
            end
        end
        for combn in combns3
            # put combination in order
            sorted_combn = sort([sel_hand[combn[1]].rank, sel_hand[combn[2]].rank, sel_hand[combn[3]].rank])
            # run of 3: if the absolute difference between cards 1 and 2 is one and the abs diff of cards 2 and 3 is one
            if abs(diff([sorted_combn[1], sorted_combn[2]])[1]) == 1 && abs(diff([sorted_combn[2], sorted_combn[3]])[1]) == 1
                push!(runs, 3::Int)
            end
            # check for 3 card 15s
            if sel_hand[combn[1]].value + sel_hand[combn[2]].value + sel_hand[combn[3]].value == 15
                push!(fifteens, 2::Int)
            end
        end
        for combn in full_hand
            # put combination in order
            sorted_combn = sort([sel_hand[combn[1]].rank, sel_hand[combn[2]].rank, sel_hand[combn[3]].rank, sel_hand[combn[4]].rank])
            # run of 4: same logic as run of 3
            if abs(diff([sorted_combn[1], sorted_combn[2]])[1]) == 1 && abs(diff([sorted_combn[2],sorted_combn[3]])[1]) == 1 && abs(diff([sorted_combn[3],sorted_combn[4]])[1]) == 1
                push!(runs, 4::Int)
            end
            # check for flush
            if sel_hand[combn[1]].suit == sel_hand[combn[2]].suit && sel_hand[combn[2]].suit == sel_hand[combn[3]].suit && sel_hand[combn[3]].suit == sel_hand[combn[4]].suit
                push!(flush, 4::Int)
            end
            # check for 4 card 15s
            if sel_hand[combn[1]].value + sel_hand[combn[2]].value + sel_hand[combn[3]].value + sel_hand[combn[4]].value == 15
                push!(fifteens, 2::Int)
            end
        end
        push!(hand_scores, sum(vcat(fifteens, pairs, runs, flush)))
    end
    # grab the first hand in the list with the maximum number of points
    # future versions could include a "smarter" selection process, e.g.
    # given the hand Q 5 8 3 9 2, the algorithm currently picks Q 5 8 2 (4 pts) vs Q 5 2 3 (4 pts, ~10% potential for run)
    # Desirable to implement a modifier that gives additional weight to logical combinations of cards
    # Not worthwhile to implement probability maximization--not realistic to most cribbage games
    scored_hand = hand(hand_combn[findfirst(x->x == maximum(hand_scores), hand_scores)], "Scored Hand")
    return scored_hand
end

function peg(scored_hand::hand, peg_pile::hand, pile_score::Vector{Int64}, s_card, s_reason, passed_p1::Vector{Bool}, passed_p2::Vector{Bool}, turn::Vector{Int})

    player = sum(turn) % 2 == 0 ? 2::Int : 1::Int
    # get all legal plays
    pos_plays = Bool[]
    for c in 1:length(scored_hand.cards)
        push!(pos_plays, scored_hand.cards[c].value + sum(pile_score) <= 31)
    end
    # pick pegging choice that yields max points
    if any(pos_plays)
        card_scores = Int[]
        score_reasons = String[]
        # check--are top two cards of pegging stack a pair?
        if length(peg_pile.cards) >= 2
            top_pair = peg_pile.cards[length(peg_pile.cards)].rank == peg_pile.cards[length(peg_pile.cards)-1].rank
        else
            top_pair = false
        end
        # check--if top cards are a pair, is it a triple?
        if top_pair && length(peg_pile.cards) >= 3
            top_trip = peg_pile.cards[length(peg_pile.cards)-1].rank == peg_pile.cards[length(peg_pile.cards)-2].rank
        else
            top_trip = false
        end
        # iterate over possible plays
        for play in 1:length(pos_plays)
            if pos_plays[play] == true
                fifteens = Int[]
                pairs = Int[]
                runs = Int[]
                thirty_one = Int[]
                reason = String[]

                if scored_hand.cards[play].value + sum(pile_score) == 15
                    push!(fifteens, 2::Int)
                    push!(reason, "f_")
                end

                if scored_hand.cards[play].value + sum(pile_score) == 31
                    push!(thirty_one, 2::Int)
                    push!(reason, "t_")
                end

                if length(peg_pile.cards) >= 1 && !top_pair && !top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
                    push!(pairs, 2::Int)
                    push!(reason, "p_")
                end

                if length(peg_pile.cards) >= 2 && top_pair && !top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
                    push!(pairs, 6::Int)
                    push!(reason, "p6_")
                end

                if top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
                    push!(pairs, 12::Int)
                    push!(reason, "p12_")
                end
                # checks for runs up to length 4--it would be possible to go deeper, but for the time being I arrived at 4 as a realistic "max" run depth
                # after validation, doable to add checks for greater depth
                if !top_pair && length(peg_pile.cards) >= 3
                    sorted_stack = sort([scored_hand.cards[play].rank, peg_pile.cards[length(peg_pile.cards)].rank, peg_pile.cards[length(peg_pile.cards)-1].rank, peg_pile.cards[length(peg_pile.cards)-2].rank])
                    if abs(diff([sorted_stack[1], sorted_stack[2]])[1]) == 1 && abs(diff([sorted_stack[2],sorted_stack[3]])[1]) == 1 && abs(diff([sorted_stack[3],sorted_stack[4]])[1]) == 1
                        push!(runs, 4::Int)
                        push!(reason, "r4_")
                        is_r4 = true
                    else
                        is_r4 = false
                    end
                else
                    is_r4 = false
                end

                if !top_pair && !is_r4 && length(peg_pile.cards) >= 2
                    sorted_stack = sort([scored_hand.cards[play].rank, peg_pile.cards[length(peg_pile.cards)].rank, peg_pile.cards[length(peg_pile.cards)-1].rank])
                    if abs(diff([sorted_stack[1], sorted_stack[2]])[1]) == 1 && abs(diff([sorted_stack[2],sorted_stack[3]])[1]) == 1
                        push!(runs, 3::Int)
                        push!(reason, "r3_")
                    end
                end

                push!(card_scores, sum(vcat(fifteens, pairs, runs, thirty_one)))

                full_reason = ""
                # concatenate reasons into single string
                for r in reason
                    full_reason = r*full_reason
                end
                push!(score_reasons, full_reason)
            else
                push!(card_scores, -1)
                push!(score_reasons, "")
            end
        end
        push!(peg_pile, scored_hand.cards[findfirst(x->x == maximum(card_scores), card_scores)])
        push!(pile_score, scored_hand.cards[findfirst(x->x == maximum(card_scores), card_scores)].value)
        if maximum(card_scores) > 0
            push!(s_card, scored_hand.cards[findfirst(x->x == maximum(card_scores), card_scores)].rank)
            push!(s_reason, score_reasons[findfirst(x->x == maximum(card_scores), card_scores)])
            #push!(h_idx, idx)
        end
        deleteat!(scored_hand, findfirst(x->x == maximum(card_scores), card_scores))
        if sum(pile_score) == 31
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end

            deleteat!(passed_p1, 1)
            push!(passed_p1, false)
            deleteat!(passed_p2, 1)
            push!(passed_p2, false)
        end
        push!(turn, 1)
    elseif !any(pos_plays)
        if player == 1 && passed_p2[1] == true
            # reset pile score, pegging pile, passed tracker, advance turn
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end
            deleteat!(passed_p2, 1)
            push!(passed_p2, false)
            push!(turn, 1)

        elseif player == 2 && passed_p1[1] == true
            # reset pile score, pegging pile, passed tracker, advance turn
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end
            deleteat!(passed_p1, 1)

            push!(passed_p1, false)
            push!(turn, 1)

        elseif player == 1 && passed_p2[1] == false
            deleteat!(passed_p1, 1)
            push!(passed_p1, true)
            push!(turn, 1)
        else player == 2 && passed_p1[1] == false
            deleteat!(passed_p2, 1)
            push!(passed_p2, true)
            push!(turn, 1)
        end
    end
end

function peg_random(scored_hand::hand, peg_pile::hand, pile_score::Vector{Int64}, s_card, s_reason, passed_p1::Vector{Bool}, passed_p2::Vector{Bool}, turn::Vector{Int})
    player = sum(turn) % 2 == 0 ? 2::Int : 1::Int
    # get all legal plays
    pos_plays = Bool[]
    for c in 1:length(scored_hand.cards)
        push!(pos_plays, scored_hand.cards[c].value + sum(pile_score) <= 31)
    end
    if any(pos_plays)
        play = findfirst(x->x == true, pos_plays)

        reason = String[]
            # check--are top two cards of pegging stack a pair?
        if length(peg_pile.cards) >= 2
            top_pair = peg_pile.cards[length(peg_pile.cards)].rank == peg_pile.cards[length(peg_pile.cards)-1].rank
        else
            top_pair = false
        end
            # check--if top cards are a pair, is it a triple?
        if top_pair && length(peg_pile.cards) >= 3
            top_trip = peg_pile.cards[length(peg_pile.cards)-1].rank == peg_pile.cards[length(peg_pile.cards)-2].rank
        else
            top_trip = false
        end

        reason = String[]

        if scored_hand.cards[play].value + sum(pile_score) == 15
            push!(reason, "f_")
        end

        if scored_hand.cards[play].value + sum(pile_score) == 31
            push!(reason, "t_")
        end

        if length(peg_pile.cards) >= 1 && !top_pair && !top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
            push!(reason, "p_")
        end

        if length(peg_pile.cards) >= 2 && top_pair && !top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
            push!(reason, "p6_")
        end

        if top_trip && scored_hand.cards[play].rank == peg_pile.cards[length(peg_pile.cards)].rank
            push!(reason, "p12_")
        end
        # checks for runs up to length 4--it would be possible to go deeper, but for the time being I arrived at 4 as a realistic "max" run depth
        # after validation, doable to add checks for greater depth
        if !top_pair && length(peg_pile.cards) >= 3
            sorted_stack = sort([scored_hand.cards[play].rank, peg_pile.cards[length(peg_pile.cards)].rank, peg_pile.cards[length(peg_pile.cards)-1].rank, peg_pile.cards[length(peg_pile.cards)-2].rank])
            if abs(diff([sorted_stack[1], sorted_stack[2]])[1]) == 1 && abs(diff([sorted_stack[2],sorted_stack[3]])[1]) == 1 && abs(diff([sorted_stack[3],sorted_stack[4]])[1]) == 1
                push!(reason, "r4_")
                is_r4 = true
            else
                is_r4 = false
            end
        else
            is_r4 = false
        end

        if !top_pair && !is_r4 && length(peg_pile.cards) >= 2
            sorted_stack = sort([scored_hand.cards[play].rank, peg_pile.cards[length(peg_pile.cards)].rank, peg_pile.cards[length(peg_pile.cards)-1].rank])
            if abs(diff([sorted_stack[1], sorted_stack[2]])[1]) == 1 && abs(diff([sorted_stack[2],sorted_stack[3]])[1]) == 1
                push!(reason, "r3_")
            end
        end


        if length(reason) > 0
            full_reason = ""
            # concatenate reasons into single string
            for r in reason
                full_reason = r*full_reason
            end
            push!(s_reason, full_reason)
            push!(s_card, scored_hand.cards[play].rank)
        end

        push!(peg_pile, scored_hand.cards[play])
        push!(pile_score, scored_hand.cards[play].value)
        deleteat!(scored_hand, play)

        if sum(pile_score) == 31
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end
            deleteat!(passed_p1, 1)
            push!(passed_p1, false)
            deleteat!(passed_p2, 1)
            push!(passed_p2, false)
        end
        push!(turn, 1)
    elseif !any(pos_plays)
        if player == 1 && passed_p2[1] == true
            # reset pile score, pegging pile, passed tracker, advance turn
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end
            deleteat!(passed_p2, 1)
            push!(passed_p2, false)
            push!(turn, 1)

        elseif player == 2 && passed_p1[1] == true
            # reset pile score, pegging pile, passed tracker, advance turn
            for i in 1:length(pile_score)
                deleteat!(pile_score, 1)
            end
            for i in 1:length(peg_pile.cards)
                deleteat!(peg_pile.cards, 1)
            end
            deleteat!(passed_p1, 1)
            push!(passed_p1, false)
            push!(turn, 1)

        elseif player == 1 && passed_p2[1] == false
            deleteat!(passed_p1, 1)
            push!(passed_p1, true)
            push!(turn, 1)
        else player == 2 && passed_p1[1] == false
            deleteat!(passed_p2, 1)
            push!(passed_p2, true)
            push!(turn, 1)
        end
    end
end
###########################################################
# RANDOM HAND, RANDOM PEGGING
###########################################################
full_rand_s_card = Int[]
full_rand_s_reason = String[]
for i in 1:1000000
    cribbage_deck = deck()
    shuffle!(cribbage_deck)

    hand1 = hand()
    hand2 = hand()
    # random 4 card hands
    move!(cribbage_deck, hand1, 4)
    move!(cribbage_deck, hand2, 4)

    peg_pile = hand()
    pile_score = Int[]

    passed_p1 = Bool[false]
    passed_p2 = Bool[false]
    # init pegging
    push!(peg_pile, hand1.cards[1])
    push!(pile_score, hand1.cards[1].value)
    deleteat!(hand1, 1)

    turn = Int[2]

    while length(hand1.cards) + length(hand2.cards) > 0
        if sum(turn) % 2 == 0
            peg_random(hand2, peg_pile, pile_score, full_rand_s_card, full_rand_s_reason, passed_p1, passed_p2, turn)
        else
            peg_random(hand1, peg_pile, pile_score, full_rand_s_card, full_rand_s_reason, passed_p1, passed_p2, turn)
        end
    end
end

###########################################################
# RANDOM HAND, PEGGING STRATEGY
###########################################################
rh_s_card = Int[]
rh_s_reason = String[]
for i in 1:1000000
    cribbage_deck = deck()
    shuffle!(cribbage_deck)

    hand1 = hand()
    hand2 = hand()

    move!(cribbage_deck, hand1, 4)
    move!(cribbage_deck, hand2, 4)

    peg_pile = hand()
    pile_score = Int[]

    passed_p1 = Bool[false]
    passed_p2 = Bool[false]

    # init pegging
    lead_plays = Bool[]
    for c in 1:length(hand1.cards)
        push!(lead_plays, hand1.cards[c].value != 5)
    end
    if any(lead_plays)
        push!(peg_pile, hand1.cards[findfirst(x->x == true, lead_plays)])
        push!(pile_score, hand1.cards[findfirst(x->x == true, lead_plays)].value)
        deleteat!(hand1, findfirst(x->x == true, lead_plays))
    else
        push!(peg_pile, hand1.cards[1])
        push!(pile_score, hand1.cards[1].value)
        deleteat!(hand1, 1)
    end
    # sort hands high to low
    sort!(hand1.cards, rev = true)
    sort!(hand2.cards, rev = true)

    turn = Int[2]

    while length(hand1.cards) + length(hand2.cards) > 0
        if sum(turn) % 2 == 0
            peg(hand2, peg_pile, pile_score, rh_s_card, rh_s_reason, passed_p1, passed_p2, turn)
        else
            peg(hand1, peg_pile, pile_score, rh_s_card, rh_s_reason, passed_p1, passed_p2, turn)
        end
    end
end
###########################################################
# STRATEGY: PICK HIGHEST SCORING HAND & PEG FOR MOST POINTS
###########################################################
s_card = Int[]
s_reason = String[]
@time for i in 1:1000000
    cribbage_deck = deck()
    shuffle!(cribbage_deck)

    hand1 = hand()
    hand2 = hand()

    move!(cribbage_deck, hand1, 6)
    move!(cribbage_deck, hand2, 6)

    h1_combns = combinations(hand1.cards, 4) |> collect
    h2_combns = combinations(hand2.cards, 4) |> collect
    hand1 = score_hand(h1_combns)
    hand2 = score_hand(h2_combns)

    peg_pile = hand()
    pile_score = Int[]

    passed_p1 = Bool[false]
    passed_p2 = Bool[false]

    # init pegging
    lead_plays = Bool[]
    for c in 1:length(hand1.cards)
        push!(lead_plays, hand1.cards[c].value != 5)
    end
    if any(lead_plays)
        push!(peg_pile, hand1.cards[findfirst(x->x == true, lead_plays)])
        push!(pile_score, hand1.cards[findfirst(x->x == true, lead_plays)].value)
        deleteat!(hand1, findfirst(x->x == true, lead_plays))
    else
        push!(peg_pile, hand1.cards[1])
        push!(pile_score, hand1.cards[1].value)
        deleteat!(hand1, 1)
    end
    # sort hands high to low
    sort!(hand1.cards, rev = true)
    sort!(hand2.cards, rev = true)

    turn = Int[2]

    while length(hand1.cards) + length(hand2.cards) > 0
        if sum(turn) % 2 == 0
            peg(hand2, peg_pile, pile_score, s_card, s_reason, passed_p1, passed_p2, turn)
        else
            peg(hand1, peg_pile, pile_score, s_card, s_reason, passed_p1, passed_p2, turn)
        end
    end
end

###########################################################
# WRITE OUT RESULTS
###########################################################
CSV.write("full_random_prelim.csv", DataFrame(score_card = full_rand_s_card, score_reason = full_rand_s_reason))
CSV.write("random_hand_control_data_prelim.csv", DataFrame(score_card = rh_s_card, score_reason = rh_s_reason))
CSV.write("prelim_hand_data.csv", DataFrame(score_card = s_card, score_reason = s_reason))
