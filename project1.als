/*
 * 17-651 | Group Project | Team 9
 */

/*
 * General Idea: 
 *
 * We don't need to build models of abstract social networks
 * We just take care of our Nicebook
 * That is, for example, the "User" set means all users of Nicebook
 *
 */

/*
 * All pieces of content in Nicebook
 * Three different types: Note, Photo, Comment
 */
abstract sig Content {
	// Content must be uploaded by only one user
	uploadedBy: one User,
	// User can only tag one another
	tags: User -> one User,
	// The privacy level of this Content
	// MUST BE DEFINED when uploaded
	privacy: one PrivacyLevel,
}

sig Note extends Content {
	// Only notes can contain photos
	contain: set Photo,
}
sig Photo extends Content {}
sig Comment extends Content {
	attachedTo: one Content,
}

/*
 * Set of all users using Nicebook
 *
 * For a user's content published content
 * privacySettingView: Marks the set of users that can view them
 * privacySettingComment: Marks the set of users that can comment them
 *
 * Tips when writing predicates like "addComment"
 * 1. first check whether the content is published on the wall
 * 2. then check privacy level to see whether the viewer
 *    is in the smaller set. (Content PL & Owner PL)
 * 3. add comment by using pre/post conditions
 * 
 * PLEASE CHECK THE WHOLE WRITE-UP
 * Not everything is in the description of operations,
 * nor in this already done structure.
 *
 * For "addComment", for example:
 * "A user can add a comment only to a piece of content 
 * that it owns or is visible on another user’s wall."
 * Please implement all checks 
 * 
 */
sig User {
	// Set of this User's friends
	friends: set User,
	// This User's uniqueWall
	uniqueWall: one Wall,
	// This User's privacy setting
	privacySettingView: one PrivacyLevel,
	privacySettingComment: one PrivacyLevel,
}

/*
 * Set of all walls in Nicebook
 */
sig Wall {
	publication: set Content,
}

/*
 * Abstract set of privacy levels
 */
abstract sig PrivacyLevel {}

/*
 * Each privacy level only have one instance
 */

// u : User
one sig OnlyMe extends PrivacyLevel {}
// u.friends + u
one sig Friends extends PrivacyLevel {} 
// u.friends.friends + u.friends (u already in this set)
one sig FriendsOfFriends extends PrivacyLevel {}
// User
one sig Everyone extends PrivacyLevel {}

/*
 * Invariants
 */
pred invariant {
	// Every wall has an owner
//	all w : Wall | w in User.uniqueWall
	// Owner of each wall must be unique
	all u1, u2 : User | (u1.uniqueWall = u2.uniqueWall) implies
		(u1 = u2)
	// Only owner's content can be published on owner's wall
	all w : Wall | all c : w.publication |
		c.uploadedBy = uniqueWall.w

	// Friendship is a symmetric relation
	all u1, u2 : User | (u2 in u1.friends) implies
		(u1 in u2.friends)
	// A user cannot be its own friend.
	no u : User | u in u.friends

	// Tagging only allowed for photos and notes
	all c : Comment | no c.tags
	// A user can be tagged only by its friends.
	all c : Content, u1, u2 : User | 
		((u1->u2) in c.tags) implies (u1 in u2.friends)
}

pred publish[c :Content, u : User] {
	// if a content is owned  by the user u, and its a note or photo
	// and it is not already on the user's wall, publish it to the wall
	all w, w' : u.uniqueWall | (c in (uploadedBy.u)) and (c not in Comment)
		and (c not in w.publication) implies w'.publication = w.publication + c
	// if a content is owned  by the user's friend, and its a note or photo
	// and it is not already on the friend's wall, publish it to the wall
	all w, w' : u.uniqueWall | (c in (uploadedBy.(u.friends))) and (c not in Comment)
		and (c not in w.publication) implies w'.publication = w.publication + c
}

pred unpublish[c : Content, u : User] {
	// if c is in the user u's wall and it is an uploaded content, unpublish
	// and remove the content from the user's account
	all w, w' : u.uniqueWall, cl, cl' : uploadedBy.u |
		c in (w.publication) and c in cl
		implies w'.publication = w.publication - c and cl' = cl - c 
//		and remove[c, u]
	// if c is in the user u's wall but it is not uploaded, just unpublish it
	all w, w' : u.uniqueWall, cl, cl' : uploadedBy.u |
		c in (w.publication) and c not in cl
		implies w'.publication = w.publication - c 	
}

run {
	invariant
} for 3
