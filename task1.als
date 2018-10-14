/*
 * 17-651 | Group Project | Team 9
 */

/*
 * Something to discuss (2018/10/14)
 * 1. Do we need something like "one sig Nicebook {...}"?
 * 2. If we do, how do we modify our code?
 */

/*
 * Three different types of content
 */
abstract sig Content{
	// Content must be uploaded by only one user
	uploadedBy: one User,
	// User can only tag one another
	tags: User -> one User,
}

sig Note extends Content{
	// Only notes can contain photos
	contain: set Photo,
}

sig Photo extends Content{}

sig Comment extends Content{
	attachedTo: one Content,
}

/*
 * Set of users
 */
sig User {
	friends: set User,
	uniqueWall: one Wall,
}

/*
 * Set of walls
 */
sig Wall {
	publication: set Content,
}

/*
 * Invariants
 */
pred invariant {
	// Every wall has an owner
	all w : Wall | w in User.uniqueWall
	// Owner of each wall must be unique
	all u1, u2 : User | (u1.uniqueWall = u2.uniqueWall) implies (u1 = u2)
	// Only owner's content can be published on owner's wall
	all w : Wall | all c : w.publication |
		c.uploadedBy = uniqueWall.w

	// Friendship is a symmetric relation
	all u1, u2 : User | (u2 in u1.friends) implies (u1 in u2.friends)
	// A user cannot be its own friend.
	no u : User | u in u.friends

	// Tagging only allowed for photos and notes
	all c : Comment | no c.tags
	// A user can be tagged only by its friends.
	all c : Content, u1, u2 : User | 
		((u1->u2) in c.tags) implies (u1 in u2.friends)
}

run {
	invariant
} for 3
