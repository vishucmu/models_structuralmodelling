/*
 * 	17-651 | Group Project | Group 9
 *      upload/remove content
 */

open Signature
open Invariant
open Privacy

// User u uploads content c with privacy level p
// c is before upload, c' is after upload
pred upload[n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel]
{
	// Percondition
	// u is a user of Nicebook n
	u in n.users
	// the content is not already in Nicebook n
	c not in n.contents
	// the content is uploaded by user u
	c.uploadedBy = u
	// no tags initially
	c not in n.tags.content
	// privacy level of content is p
	c.privacy = p
	// If c is a comment, it cannot be attached to any content
	c in Comment implies no c.attachedTo
	// Postcondition
	// users, walls, and tags remain unchanged
	n'.users = n.users
	n'.walls = n.walls
	n'.tags = n.tags
	// the content c is added in n'
	// if c is a note, the photos it contains will be uploaded together
	c in Note implies (n'.contents = n.contents + c + c.contain and 
		(all c' : c.contain | c.privacy = c'.privacy and c'.uploadedBy = u))
		else n'.contents = n.contents + c
	// no comment attached to c initially
	all com : n.contents | 
		com in Comment implies c not in com.attachedTo
}

// User u removes content c
pred remove[n, n' : Nicebook, u : User, c : Content] 
{
	// Precondition
	// u is a user of Nicebook n
	u in n.users
	// the content c is uploaded by user u
	c.uploadedBy = u
	// the content c is in Nicebook n
	c in n.contents
	// comments can not be removed
	c not in Comment
	// if c is a photo and is contained by a note
	// it cannot be removed independly
	not (c in Photo and (some c' : n.contents | c in c'.contain))
	// Postcondition
	// users and tags remain unchanged
	n'.users = n.users
	// remove content c from contents
	n'.contents = n.contents - c - (^attachedTo).c
	all u' : n.users | n'.walls[u'] = n.walls[u'] - c
	n'.tags = n.tags - content.c
}

// Check for upload operation
assert UploadCheck {
	all n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		(userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] 
			and upload[n, n', u, c, p]) implies nicebookInvariant[n']
}

// Check for remove operation
assert RemoveCheck {
	all n, n' : Nicebook, c : Content, u : User | 
		(userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] 
			and remove[n, n', u, c]) implies nicebookInvariant[n']
}

run runContent {
	all n : Nicebook | nicebookInvariant[n]
	some n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		upload[n, n', u, c, p] and userInvariant[n, u] and contentInvariant[n, c] and 
		nicebookInvariant[n] and nicebookInvariant[n']
	some n, n' : Nicebook, c : Content, u : User | remove[n, n', u, c] and 
		userInvariant[n, u] and contentInvariant[n, c] and 
		nicebookInvariant[n] and nicebookInvariant[n']
} for 12 but exactly 3 Nicebook

check UploadCheck for 12 but exactly 2 Nicebook
check RemoveCheck for 12 but exactly 2 Nicebook
