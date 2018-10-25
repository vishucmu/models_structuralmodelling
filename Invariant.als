/*
 * 	17-651 | Group Project | Team 9
 */

open Signature

pred nicebookInvariant[n : Nicebook] {
	// no user can have wall without being Nicebook's user
	no u : User | u not in n.users and (some c : Content | c = n.walls[u])
	// every content in the wall should exist in the Nicebook
	// and it can not be a comment (comment can not exist without
	// attach to some content)
	all u : n.users | all c : n.walls[u] | c in n.contents
		and c not in Comment and c.uploadedBy in u + u.friends
	// all contents of the Nicebook should follow the invariants of contents
	all c : n.contents | contentInvariant[c]
	// all users using the wall should follow the invariants of users
	all u : n.users | userInvariant[u]
	// all tags of the Nicebook should follow the invariants of tags
	all t : n.tags | tagInvariant[n, t]
}

pred userInvariant[u : User] {
	// friendship is a symmetric relation
	all u' : User | u in u'.friends iff u' in u.friends and u != u'
	// a user cannot be his/her own friend.
	not u in u.friends
}

pred contentInvariant[c : Content] {
	// comments should follow its invariants
	c in Comment implies commentInvariant[c]
	// photos and notes have privacy level
	one p : PrivacyLevel | p = c.privacy
	// notes should follow its invariants
	c in Note implies noteInvariant[c]
}

pred commentInvariant[c : Comment] {
	// comments have no privacy level	
	no c.privacy 
	// comments can not be attached to itself recursively
	c not in c.^attachedTo
}

pred tagInvariant[n : Nicebook, t : Tag] {
	// a user can not tag him/herself
	t.tagger != t.taggee
	// both tagger and taggee must be users in Nicebook
	t.tagger in n.users
	t.taggee in n.users
	// the content associated with the tag must be with the Nicebook
	t.content in n.contents
	// a user can not tag a comment
	t.content not in Comment
}

// Notes' privacy level should be same as all its photos (assumption)
pred noteInvariant[c : Note] {
	all c' : c.contain | c.privacy = c'.privacy
}
